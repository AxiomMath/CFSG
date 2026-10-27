module

public import CFSG.RankThree.PartTwo.Sec10.Item107ProofBad
public import CFSG.RankThree.PartTwo.Sec10.Item107ProofJordan

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item107Proof

section General

variable {G : Type*} [Group G]

theorem mem_normalizer_of_conj_mem [Finite G] {Q : Subgroup G} {y : G}
    (h : ∀ q ∈ Q, y * q * y⁻¹ ∈ Q) : y ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨q, hq, rfl⟩
    exact h q hq
  · rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]

theorem exists_transvSubgroup (c : G) (E : Subgroup G) :
    ∃ T : Subgroup G, ∀ m, m ∈ T ↔ (∀ e ∈ E, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ E := by
  refine ⟨{ carrier := {m | (∀ e ∈ E, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ E}
            one_mem' := ⟨fun e _ => by group, by simp⟩
            mul_mem' := ?_
            inv_mem' := ?_ }, fun m => Iff.rfl⟩
  · rintro m m' ⟨hmE, hmc⟩ ⟨hm'E, hm'c⟩
    refine ⟨fun e he => ?_, ?_⟩
    · calc m * m' * e * (m * m')⁻¹ = m * (m' * e * m'⁻¹) * m⁻¹ := by group
        _ = e := by rw [hm'E e he, hmE e he]
    · have h1 : m * m' * c * (m * m')⁻¹ * c⁻¹ =
          (m * (m' * c * m'⁻¹ * c⁻¹) * m⁻¹) * (m * c * m⁻¹ * c⁻¹) := by group
      rw [h1, hmE _ hm'c]
      exact E.mul_mem hm'c hmc
  · rintro m ⟨hmE, hmc⟩
    refine ⟨fun e he => ?_, ?_⟩
    · calc m⁻¹ * e * m⁻¹⁻¹ = m⁻¹ * (m * e * m⁻¹) * m := by rw [hmE e he]; group
        _ = e := by group
    · have h1 : m⁻¹ * c * m⁻¹⁻¹ * c⁻¹ = m⁻¹ * (m * c * m⁻¹ * c⁻¹)⁻¹ * m := by group
      have h2 : m⁻¹ * (m * c * m⁻¹ * c⁻¹)⁻¹ * m = (m * c * m⁻¹ * c⁻¹)⁻¹ := by
        calc m⁻¹ * (m * c * m⁻¹ * c⁻¹)⁻¹ * m =
            m⁻¹ * (m * (m * c * m⁻¹ * c⁻¹)⁻¹ * m⁻¹) * m := by
              rw [hmE _ (E.inv_mem hmc)]
          _ = (m * c * m⁻¹ * c⁻¹)⁻¹ := by group
      rw [h1, h2]
      exact E.inv_mem hmc

theorem mem_normalizer_transv [Finite G] {c : G} {E T : Subgroup G}
    (hT : ∀ m, m ∈ T ↔ (∀ e ∈ E, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ E) {y : G}
    (hyc : y * c = c * y) (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    y ∈ Subgroup.normalizer (T : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro m hm
  obtain ⟨hmE, hmc⟩ := (hT m).mp hm
  rw [hT]
  refine ⟨fun e he => ?_, ?_⟩
  · have he' : y⁻¹ * e * y ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) e).mp he
      simpa using this
    calc y * m * y⁻¹ * e * (y * m * y⁻¹)⁻¹ = y * (m * (y⁻¹ * e * y) * m⁻¹) * y⁻¹ := by group
      _ = e := by rw [hmE _ he']; group
  · have hyc' : y⁻¹ * c * y = c := by
      calc y⁻¹ * c * y = y⁻¹ * (c * y) := by group
        _ = y⁻¹ * (y * c) := by rw [hyc]
        _ = c := by group
    have h1 : y * m * y⁻¹ * c * (y * m * y⁻¹)⁻¹ * c⁻¹ =
        y * (m * (y⁻¹ * c * y) * m⁻¹ * (y⁻¹ * c * y)⁻¹) * y⁻¹ := by group
    rw [h1, hyc']
    exact (Subgroup.mem_normalizer_iff.mp hyN _).mp hmc

theorem psi_conj {c : G} {E T : Subgroup G} {ψ : T →* E}
    (hψ : ∀ m : T, ((ψ m : E) : G) = (m : G) * c * (m : G)⁻¹ * c⁻¹)
    {y : G} (hyc : y * c = c * y) (m m' : T) (hm' : (m' : G) = y * m * y⁻¹) :
    ((ψ m' : E) : G) = y * (ψ m : G) * y⁻¹ := by
  rw [hψ, hψ, hm']
  have hyc' : y⁻¹ * c * y = c := by
    calc y⁻¹ * c * y = y⁻¹ * (c * y) := by group
      _ = y⁻¹ * (y * c) := by rw [hyc]
      _ = c := by group
  calc y * m * y⁻¹ * c * (y * m * y⁻¹)⁻¹ * c⁻¹ =
      y * ((m : G) * (y⁻¹ * c * y) * (m : G)⁻¹ * (y⁻¹ * c * y)⁻¹) * y⁻¹ := by group
    _ = y * ((m : G) * c * (m : G)⁻¹ * c⁻¹) * y⁻¹ := by rw [hyc']

theorem normalizer_le_normalizer_centralizer [Finite G] {D : Subgroup G} :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  intro m hm
  apply mem_normalizer_of_conj_mem
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : m⁻¹ * u * m ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) u).mp hu
    simpa using this
  have h1 := (Subgroup.mem_centralizer_iff.mp hy) _ hu'
  calc u * (m * y * m⁻¹) = m * ((m⁻¹ * u * m) * y) * m⁻¹ := by group
    _ = m * (y * (m⁻¹ * u * m)) * m⁻¹ := by rw [h1]
    _ = m * y * m⁻¹ * u := by group

theorem mul_inv_mul_mul_inv_eq {M : Type*} [CommGroup M] (p q x : M) (hq : q ^ 3 = 1) :
    p * q⁻¹ * (x * q⁻¹) = x * q * p := by
  have h2 : q⁻¹ = q ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', hq]
  have hq' : q⁻¹ * q⁻¹ = q := by
    rw [h2, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, hq, one_mul]
  calc p * q⁻¹ * (x * q⁻¹) = (p * x) * (q⁻¹ * q⁻¹) := mul_mul_mul_comm p q⁻¹ x q⁻¹
    _ = (p * x) * q := by rw [hq']
    _ = x * q * p := by rw [mul_comm p x, mul_assoc, mul_comm p q, ← mul_assoc]

theorem transv_le_normalizer_E [Finite G] {c : G} {E T : Subgroup G}
    (hT : ∀ m, m ∈ T ↔ (∀ e ∈ E, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ E) :
    T ≤ Subgroup.normalizer (E : Set G) := fun m hm =>
  mem_normalizer_of_conj_mem fun e he => by rw [((hT m).mp hm).1 e he]; exact he

theorem exists_isSylowOf_normalized [Finite G] {T : Subgroup G} {a : G}
    (haT : a ∈ Subgroup.normalizer (T : Set G)) (ha3 : a ^ 3 = 1) :
    ∃ Q : Subgroup G, IsSylowOf 3 Q T ∧ a ∈ Subgroup.normalizer (Q : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := T ⊔ Subgroup.zpowers a with hK
  have hKN : K ≤ Subgroup.normalizer (T : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr haT)
  have ha3' : IsPGroup 3 (Subgroup.zpowers a) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
  obtain ⟨P, hP⟩ := (ha3'.comap_subtype (K := K)).exists_le_sylow
  have hPsyl : IsSylowOf 3 ((P : Subgroup K).map K.subtype) K := ⟨P, rfl⟩
  have haP : a ∈ (P : Subgroup K).map K.subtype :=
    ⟨⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers a)⟩,
      hP (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers a)), rfl⟩
  refine ⟨(P : Subgroup K).map K.subtype ⊓ T, hPsyl.inf_of_le_normalizer le_sup_left hKN, ?_⟩
  apply mem_normalizer_of_conj_mem
  intro q hq
  exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ haP hq.1) (Subgroup.inv_mem _ haP),
    (Subgroup.mem_normalizer_iff.mp haT q).mp hq.2⟩

theorem irreducible_conj [Finite G] {E : Subgroup G} (hE : Nat.card E = 27) {x : G}
    (hx13 : x ^ 13 = 1) (hxfix : ∀ e ∈ E, x * e * x⁻¹ = e → e = 1)
    (hxN : x ∈ Subgroup.normalizer (E : Set G)) (V : Subgroup E)
    (hV : ∀ t ∈ V, (E.normalizerMonoidHom ⟨x, hxN⟩).toMonoidHom t ∈ V) : V = ⊥ ∨ V = ⊤ := by
  set V' := V.map E.subtype with hV'
  have hV'E : V' ≤ E := Subgroup.map_subtype_le V
  have hxV' : x ∈ Subgroup.normalizer (V' : Set G) := mem_normalizer_of_conj_mem (by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨_, hV t ht, rfl⟩)
  rcases eq_bot_or_eq_of_le_normalizer hE hx13 hxfix hV'E hxV' with h1 | h1
  · left
    exact (Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).mp h1
  · right
    rw [eq_top_iff]
    intro t _
    have ht : (t : G) ∈ V' := by rw [h1]; exact t.2
    obtain ⟨t', ht', htt'⟩ := ht
    have htt : t' = t := Subtype.ext htt'
    exact htt ▸ ht'

end General

section Std


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem transv_le_normalizer_D (h : Sec10Std G A c L a R) {T : Subgroup G}
    (hT : ∀ m, m ∈ T ↔ (∀ e ∈ R ⊓ L, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L) :
    T ≤ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G) := by
  intro m hm
  apply mem_normalizer_of_conj_mem
  intro u hu
  obtain ⟨hmE, hmc⟩ := (hT m).mp hm
  obtain ⟨k, e, he, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers
    (fun z hz => h.commute_c_of_mem_inf hz) hu
  have hcD : m * c * m⁻¹ ∈ sec10D c R L := by
    have h1 : m * c * m⁻¹ = (m * c * m⁻¹ * c⁻¹) * c := by group
    rw [h1]
    exact Subgroup.mul_mem _ (h.inf_le_D hmc) h.c_mem_D
  have h1 : m * (c ^ k * e) * m⁻¹ = (m * c * m⁻¹) ^ k * (m * e * m⁻¹) := by
    rw [conj_zpow]
    group
  rw [h1, hmE e he]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ hcD k) (h.inf_le_D he)

theorem centralizer_D_le_transv (h : Sec10Std G A c L a R) {T : Subgroup G}
    (hT : ∀ m, m ∈ T ↔ (∀ e ∈ R ⊓ L, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L) :
    Subgroup.centralizer ((sec10D c R L : Subgroup G) : Set G) ≤ T := by
  intro m hm
  rw [hT]
  have hcom := Subgroup.mem_centralizer_iff.mp hm
  refine ⟨fun e he => ?_, ?_⟩
  · rw [← hcom e (h.inf_le_D he), mul_inv_cancel_right]
  · rw [← hcom c h.c_mem_D, mul_inv_cancel_right, mul_inv_cancel]
    exact (R ⊓ L).one_mem

theorem exists_psi (h : Sec10Std G A c L a R) {T : Subgroup G}
    (hT : ∀ m, m ∈ T ↔ (∀ e ∈ R ⊓ L, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L) :
    ∃ ψ : T →* (R ⊓ L : Subgroup G), ∀ m : T,
      ((ψ m : (R ⊓ L : Subgroup G)) : G) = (m : G) * c * (m : G)⁻¹ * c⁻¹ := by
  have hEcomm : ∀ x y : G, x ∈ R ⊓ L → y ∈ R ⊓ L → x * y = y * x := fun x y hx hy =>
    congrArg Subtype.val (h.isElemAbelian_inf.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨{ toFun := fun m => ⟨(m : G) * c * (m : G)⁻¹ * c⁻¹, ((hT m).mp m.2).2⟩
            map_one' := by ext; simp
            map_mul' := fun m m' => ?_ }, fun m => rfl⟩
  obtain ⟨hmE, hmc⟩ := (hT m).mp m.2
  obtain ⟨-, hm'c⟩ := (hT m').mp m'.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have h1 : (m : G) * m' * c * ((m : G) * m')⁻¹ * c⁻¹ =
      ((m : G) * ((m' : G) * c * (m' : G)⁻¹ * c⁻¹) * (m : G)⁻¹) *
        ((m : G) * c * (m : G)⁻¹ * c⁻¹) := by group
  rw [h1, hmE _ hm'c]
  exact hEcomm _ _ hm'c hmc

theorem psi_surjective (h : Sec10Std G A c L a R) {T : Subgroup G}
    (hT : ∀ m, m ∈ T ↔ (∀ e ∈ R ⊓ L, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L)
    {ψ : T →* (R ⊓ L : Subgroup G)}
    (hψ : ∀ m : T, ((ψ m : (R ⊓ L : Subgroup G)) : G) = (m : G) * c * (m : G)⁻¹ * c⁻¹)
    (hgood : ∀ e ∈ R ⊓ L, ∃ m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G),
      (∀ e' ∈ R ⊓ L, m * e' * m⁻¹ = e') ∧ m * c * m⁻¹ = c * e) :
    Function.Surjective ψ := by
  rintro ⟨e, he⟩
  obtain ⟨m, -, hmE, hmc⟩ := hgood e he
  have hce : c * e = e * c := (h.commute_c_of_mem_inf he).symm
  have hmT : m ∈ T := by
    rw [hT]
    refine ⟨hmE, ?_⟩
    rw [hmc, hce, mul_inv_cancel_right]
    exact he
  refine ⟨⟨m, hmT⟩, Subtype.ext ?_⟩
  rw [hψ]
  change m * c * m⁻¹ * c⁻¹ = e
  rw [hmc, hce, mul_inv_cancel_right]

theorem R_le_normalizer_inf (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R) :
    R ≤ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
  intro r hr
  apply mem_normalizer_of_conj_mem
  intro u hu
  exact ⟨R.mul_mem (R.mul_mem hr hu.1) (R.inv_mem hr),
    (Subgroup.mem_normalizer_iff.mp (h.R_le_normalizer h45 hr) u).mp hu.2⟩

theorem false_of_isSylowOf_top (h45 : Sec4.Item4_5) (h : Sec10Std G A c L a R) {T : Subgroup G}
    (hT : ∀ m, m ∈ T ↔ (∀ e ∈ R ⊓ L, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L)
    {ψ : T →* (R ⊓ L : Subgroup G)}
    (hψ : ∀ m : T, ((ψ m : (R ⊓ L : Subgroup G)) : G) = (m : G) * c * (m : G)⁻¹ * c⁻¹)
    (hsurj : Function.Surjective ψ) (hsyl : IsSylowOf 3 R ⊤) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRN : R ≤ Subgroup.normalizer (T : Set G) := fun r hr =>
    mem_normalizer_transv hT (Subgroup.mem_centralizer_singleton_iff.mp (h.R_le_centralizer hr))
      (R_le_normalizer_inf h45 h hr)
  have h1 : IsSylowOf 3 R (T ⊔ R) := hsyl.of_le le_sup_right le_top
  have h2 : IsSylowOf 3 (R ⊓ T) T :=
    h1.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hRN)
  obtain ⟨Q, hQ⟩ := h2
  set S := Q.mapSurjective hsurj with hS
  have hSbot : (S : Subgroup (R ⊓ L : Subgroup G)) = ⊥ := by
    rw [hS, Sylow.coe_mapSurjective, Subgroup.eq_bot_iff_forall]
    rintro _ ⟨q, hq, rfl⟩
    have hqR : (q : G) ∈ R := by
      have h3 : (q : G) ∈ (Q : Subgroup T).map T.subtype := ⟨q, hq, rfl⟩
      rw [hQ] at h3
      exact h3.1
    have hqc : (q : G) * c = c * q :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.R_le_centralizer hqR)
    apply Subtype.ext
    rw [hψ, hqc, mul_inv_cancel_right, mul_inv_cancel]
    rfl
  have hE3 : IsPGroup 3 (⊤ : Subgroup (R ⊓ L : Subgroup G)) :=
    IsPGroup.of_card (n := 3) (by rw [Subgroup.card_top, h.card_inf]; norm_num)
  have hStop : (⊤ : Subgroup (R ⊓ L : Subgroup G)) = S := S.is_maximal' hE3 le_top
  rw [← hStop] at hSbot
  have h3 : Nat.card (⊤ : Subgroup (R ⊓ L : Subgroup G)) = 1 := by
    rw [hSbot, Subgroup.card_bot]
  rw [Subgroup.card_top, h.card_inf] at h3
  norm_num at h3

theorem R_eq_of_surjective (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    {T : Subgroup G}
    (hT : ∀ m, m ∈ T ↔ (∀ e ∈ R ⊓ L, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L)
    {ψ : T →* (R ⊓ L : Subgroup G)}
    (hψ : ∀ m : T, ((ψ m : (R ⊓ L : Subgroup G)) : G) = (m : G) * c * (m : G)⁻¹ * c⁻¹)
    (hsurj : Function.Surjective ψ) : R = Subgroup.zpowers a ⊔ sec10D c R L := by
  obtain ⟨-, -, -, hcase⟩ := rank3II_10_2 h45 h97 G A c L a R h
  rcases hcase with ⟨-, hR⟩ | ⟨-, hsyl⟩
  · exact hR
  · exact (false_of_isSylowOf_top h45 h hT hψ hsurj hsyl).elim

theorem isSylowOf_D (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    (hR : R = Subgroup.zpowers a ⊔ sec10D c R L) :
    IsSylowOf 3 (sec10D c R L) (Subgroup.centralizer ((sec10D c R L : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := sec10D c R L with hD
  have hDe := h.isElemAbelian_D
  have hDR : D ≤ R := by
    rw [hR]
    exact le_sup_right
  have hDC : D ≤ Subgroup.centralizer (D : Set G) := fun u hu => by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (hDe.1.is_comm.comm ⟨v, hv⟩ ⟨u, hu⟩)
  have haM : a ∈ Subgroup.normalizer (D : Set G) :=
    mem_normalizer_D_of h (h.comm h.a_mem h.mem_A) h.a_mem_normalizer_inf
  obtain ⟨e₁, he₁, hae₁⟩ := exists_not_commute_a h97 h
  have hnot : ∀ y : G, y ∈ Subgroup.centralizer (D : Set G) → y * e₁ * y⁻¹ = e₁ := by
    intro y hy
    rw [← (Subgroup.mem_centralizer_iff.mp hy) e₁ (h.inf_le_D he₁), mul_inv_cancel_right]
  have hRC : R ⊓ Subgroup.centralizer (D : Set G) = D := by
    apply le_antisymm _ (le_inf hDR hDC)
    rintro r ⟨hrR, hrC⟩
    rw [hR] at hrR
    obtain ⟨k, y, hy, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers'
      (Subgroup.zpowers_le.mpr haM) hrR
    have hakC : a ^ k ∈ Subgroup.centralizer (D : Set G) := by
      have := (Subgroup.centralizer (D : Set G)).mul_mem hrC
        ((Subgroup.centralizer (D : Set G)).inv_mem (hDC hy))
      simpa using this
    rcases zpow_cases_of_pow_three (h.pow_three h.a_mem) k with hk | hk | hk <;>
      rw [hk] at hakC
    · rw [hk, one_mul]
      exact hy
    · exact (hae₁ (hnot a hakC)).elim
    · have ha : a = (a ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, h.pow_three h.a_mem, one_mul]
      have h1 : a ∈ Subgroup.centralizer (D : Set G) := by
        rw [ha]
        exact Subgroup.pow_mem _ hakC 2
      exact (hae₁ (hnot a h1)).elim
  have hCH : Subgroup.centralizer (D : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun y hy =>
    mem_normalizer_zpowers_of_conj_mem (by
      rw [← (Subgroup.mem_centralizer_iff.mp hy) c h.c_mem_D, mul_inv_cancel_right]
      exact Subgroup.mem_zpowers c)
  have hRN : R ≤ Subgroup.normalizer
      ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := fun r hr =>
    normalizer_le_normalizer_centralizer (mem_normalizer_D_of h
      (Subgroup.mem_centralizer_singleton_iff.mp (h.R_le_centralizer hr))
      (R_le_normalizer_inf h45 h hr))
  have h1 : IsSylowOf 3 R (R ⊔ Subgroup.centralizer (D : Set G)) :=
    h.isSylowOf.of_le le_sup_left (sup_le h.isSylowOf.le hCH)
  have h2 := h1.inf_of_le_normalizer le_sup_right (sup_le hRN Subgroup.le_normalizer)
  rwa [hRC] at h2

theorem exists_wreath_fix (h97 : Sec9.Item97) (h : Sec10Std G A c L a R) {δ : G}
    (hδ : δ ∈ R ⊓ L) (hN : δ * (a * δ * a⁻¹) * (a * (a * δ * a⁻¹) * a⁻¹) = 1) :
    ∃ z ∈ R ⊓ L, δ = z * (a * z * a⁻¹)⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hdL, hd3, hA⟩ := exists_inf_eq_zpowers h97 h.toHyp91
  set E := R ⊓ L with hE
  have hEe := h.isElemAbelian_inf
  let _ : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun x y => hEe.1.is_comm.comm x y }
  have haN : a ∈ Subgroup.normalizer (E : Set G) := h.a_mem_normalizer_inf
  set α : E →* E := (E.normalizerMonoidHom ⟨a, haN⟩).toMonoidHom with hαdef
  have hα : ∀ x : E, ((α x : E) : G) = a * x * a⁻¹ := fun x => rfl
  let f : E →* E :=
    { toFun := KFacts.commMap α
      map_one' := by simp [KFacts.commMap]
      map_mul' := fun x y => by
        simp only [KFacts.commMap, map_mul, mul_inv_rev]
        rw [mul_comm y⁻¹ x⁻¹, mul_mul_mul_comm] }
  have hf : ∀ x, f x = α x * x⁻¹ := fun _ => rfl
  have hexp : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hEe.2 x x.2)
  have hα3 : ∀ x : E, α (α (α x)) = x := by
    intro x
    apply Subtype.ext
    rw [hα, hα, hα]
    have ha3' : a * (a * a) = 1 := by rw [← pow_three]; exact h.pow_three h.a_mem
    calc a * (a * (a * (x : G) * a⁻¹) * a⁻¹) * a⁻¹ = a * (a * a) * x * (a * (a * a))⁻¹ := by
          group
      _ = x := by rw [ha3', one_mul, inv_one, mul_one]
  have hf3 : ∀ x, f (f (f x)) = 1 := by
    intro x
    change KFacts.commMap α (KFacts.commMap α (KFacts.commMap α x)) = 1
    rw [KFacts.cube_identity_mul, hα3, inv_pow, hexp, inv_one, mul_one, hexp, mul_one,
      mul_inv_cancel]
  have hff : ∀ x : E, f (f x) = x * α x * α (α x) := by
    intro x
    rw [hf, hf, map_mul, map_inv, mul_inv_rev, inv_inv]
    exact mul_inv_mul_mul_inv_eq _ _ _ (hexp _)
  have hkerc : Nat.card f.ker = 3 := by
    have hker : f.ker.map E.subtype = Subgroup.zpowers d := by
      rw [← h.inf_centralizer_a hdL hA]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : α x = x := mul_inv_eq_one.mp hx
        refine ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have h1 := congrArg Subtype.val hx'
        rw [hα] at h1
        show (x : G) * a = a * x
        calc (x : G) * a = a * x * a⁻¹ * a := by rw [h1]
          _ = a * x := by group
      · rintro ⟨hyE, hya⟩
        have hya' : y ∈ Subgroup.centralizer ({a} : Set G) := hya
        refine ⟨⟨y, hyE⟩, ?_, rfl⟩
        show (⟨y, hyE⟩ : E) ∈ f.ker
        rw [MonoidHom.mem_ker, hf, mul_inv_eq_one]
        apply Subtype.ext
        rw [hα]
        have h1 := Subgroup.mem_centralizer_singleton_iff.mp hya'
        calc a * y * a⁻¹ = y * a * a⁻¹ := by rw [h1]
          _ = y := by group
    rw [← Subgroup.card_map_of_injective E.subtype_injective, hker, Nat.card_zpowers, hd3]
  have hrange : Nat.card f.range = 9 := by
    have h1 := KFacts.card_eq_card_ker_mul_card_range f
    rw [h.card_inf, hkerc] at h1
    omega
  set f2 := f.comp f with hf2
  have hle : f.range ≤ f2.ker := by
    rintro _ ⟨x, rfl⟩
    exact hf3 x
  have hrange2 : 3 ≤ Nat.card f2.range := by
    have h1 := card_le_card_map_mul f f.range
    have h2 : f.range.map f = f2.range := by
      rw [hf2, MonoidHom.range_comp]
    rw [h2, hrange, hkerc] at h1
    omega
  have hker2 : Nat.card f2.ker ≤ 9 := by
    have h1 := KFacts.card_eq_card_ker_mul_card_range f2
    rw [h.card_inf] at h1
    by_contra hc
    push Not at hc
    have : 10 * 3 ≤ Nat.card f2.ker * Nat.card f2.range := Nat.mul_le_mul hc hrange2
    omega
  have heq : f.range = f2.ker := Subgroup.eq_of_le_of_card_ge hle (by rw [hrange]; exact hker2)
  have hδker : (⟨δ, hδ⟩ : E) ∈ f2.ker := by
    rw [MonoidHom.mem_ker, hf2, MonoidHom.comp_apply, hff]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, hα, OneMemClass.coe_one]
    exact hN
  rw [← heq] at hδker
  obtain ⟨z₀, hz₀⟩ := hδker
  refine ⟨(z₀⁻¹ : E), (z₀⁻¹ : E).2, ?_⟩
  have h1 := congrArg Subtype.val hz₀
  rw [hf] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα] at h1 ⊢
  rw [← h1]
  have hcomm : (a * (z₀ : G) * a⁻¹) * (z₀ : G)⁻¹ = (z₀ : G)⁻¹ * (a * z₀ * a⁻¹) :=
    congrArg Subtype.val (mul_comm (α z₀) z₀⁻¹)
  rw [hcomm]
  group

theorem commutator_mem_of_transv (h : Sec10Std G A c L a R) {T : Subgroup G}
    (hT : ∀ m, m ∈ T ↔ (∀ e ∈ R ⊓ L, m * e * m⁻¹ = e) ∧ m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L) {t z : G}
    (ht : t ∈ T) (hz : z ∈ sec10D c R L) : t * z * t⁻¹ * z⁻¹ ∈ R ⊓ L := by
  obtain ⟨htE, htc⟩ := (hT t).mp ht
  obtain ⟨k, e, he, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers
    (fun y hy => h.commute_c_of_mem_inf hy) hz
  obtain ⟨et, het⟩ : ∃ et, et = t * c * t⁻¹ * c⁻¹ := ⟨_, rfl⟩
  have hetE : et ∈ R ⊓ L := het ▸ htc
  have htc' : t * c * t⁻¹ = et * c := by rw [het]; group
  have hcomm : Commute et c := (h.commute_c_of_mem_inf hetE)
  have h1 : t * (c ^ k * e) * t⁻¹ * (c ^ k * e)⁻¹ =
      (t * c ^ k * t⁻¹) * (t * e * t⁻¹) * e⁻¹ * (c ^ k)⁻¹ := by group
  rw [h1, ← conj_zpow, htc', htE e he, hcomm.mul_zpow]
  have h2 : et ^ k * c ^ k * e * e⁻¹ * (c ^ k)⁻¹ = et ^ k := by group
  rw [h2]
  exact Subgroup.zpow_mem _ hetE k

theorem exists_transvection_ad (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h : Sec10Std G A c L a R) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hgood : ∀ e ∈ R ⊓ L, ∃ m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G),
      (∀ e' ∈ R ⊓ L, m * e' * m⁻¹ = e') ∧ m * c * m⁻¹ = c * e) :
    ∃ v : G, v * a * v⁻¹ = a ∧ v * d * v⁻¹ = d ∧ v * c * v⁻¹ = c * d := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hA : A = Subgroup.closure {c, a, d} := (h97 G A c L a R h.toHyp91).2 d hdL
  have hdE : d ∈ R ⊓ L := h.d_mem_inf hdL
  set D := sec10D c R L with hD
  set E := R ⊓ L with hE
  obtain ⟨T, hT⟩ := exists_transvSubgroup c E
  obtain ⟨ψ, hψ⟩ := exists_psi h hT
  have hsurj := psi_surjective h hT hψ hgood
  have hDsyl := isSylowOf_D h45 h97 h (R_eq_of_surjective h45 h97 h hT hψ hsurj)
  have hTM : T ≤ Subgroup.normalizer (D : Set G) := transv_le_normalizer_D h hT
  have hTE : T ≤ Subgroup.normalizer (E : Set G) := transv_le_normalizer_E hT
  have hCT : Subgroup.centralizer (D : Set G) ≤ T := centralizer_D_le_transv h hT
  have hDe := h.isElemAbelian_D
  have hDC : D ≤ Subgroup.centralizer (D : Set G) := fun u hu => by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (hDe.1.is_comm.comm ⟨v, hv⟩ ⟨u, hu⟩)
  have hDT : D ≤ T := hDC.trans hCT
  have hED : E ≤ D := h.inf_le_D
  have hEe := h.isElemAbelian_inf
  have hac : a * c = c * a := h.comm h.a_mem h.mem_A
  have haN : a ∈ Subgroup.normalizer (E : Set G) := h.a_mem_normalizer_inf
  have haT : a ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_transv hT hac haN
  have ha3 : a ^ 3 = 1 := h.pow_three h.a_mem
  obtain ⟨Q, hQsyl, haQ⟩ := exists_isSylowOf_normalized haT ha3
  have hQT : Q ≤ T := hQsyl.le
  have hDQ : D ≤ Q := by
    obtain ⟨Q', hQ'⟩ := hQsyl
    have : (D.subgroupOf T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDT).mpr hTM
    have hD3 : IsPGroup 3 (D.subgroupOf T) := by
      have hD3' : IsPGroup 3 D := fun u => ⟨1, Subtype.ext (by simpa using hDe.2 u u.2)⟩
      exact hD3'.comap_subtype
    have h1 := hD3.le_sylow_of_normal Q'
    intro u hu
    rw [← hQ']
    exact ⟨⟨u, hDT hu⟩, h1 (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  have hQC : Q ⊓ Subgroup.centralizer (D : Set G) = D := by
    have h1 : IsSylowOf 3 (Q ⊓ Subgroup.centralizer (D : Set G))
        (Subgroup.centralizer (D : Set G)) :=
      hQsyl.inf_of_le_normalizer hCT (hTM.trans normalizer_le_normalizer_centralizer)
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hDQ hDC)
      (by rw [h1.card_eq, hDsyl.card_eq])).symm
  set ψQ : Q →* E := ψ.comp (Subgroup.inclusion hQT) with hψQdef
  have hψQ : ∀ q : Q, ((ψQ q : E) : G) = (q : G) * c * (q : G)⁻¹ * c⁻¹ := fun q => hψ _
  have hψQsurj : Function.Surjective ψQ := by
    obtain ⟨Q', hQ'⟩ := hQsyl
    set S := Q'.mapSurjective hsurj with hS
    have hE3 : IsPGroup 3 (⊤ : Subgroup E) :=
      IsPGroup.of_card (n := 3) (by rw [Subgroup.card_top, h.card_inf]; norm_num)
    have hStop : (⊤ : Subgroup E) = S := S.is_maximal' hE3 le_top
    intro t
    have ht : t ∈ (S : Subgroup E) := hStop ▸ Subgroup.mem_top t
    rw [hS, Sylow.coe_mapSurjective] at ht
    obtain ⟨q', hq', rfl⟩ := ht
    have hq'Q : (q' : G) ∈ Q := by
      rw [← hQ']
      exact ⟨q', hq', rfl⟩
    exact ⟨⟨q', hq'Q⟩, rfl⟩
  have hψQ1 : ∀ q : Q, ψQ q = 1 ↔ (q : G) ∈ D := by
    intro q
    constructor
    · intro hq
      rw [← hQC]
      refine ⟨q.2, mem_centralizer_D_of h ?_ ((hT q).mp (hQT q.2)).1⟩
      have h1 := congrArg Subtype.val hq
      rw [hψQ] at h1
      have h2 : (q : G) * c * (q : G)⁻¹ = c := by
        simpa using congrArg (· * c) h1
      calc (q : G) * c = (q : G) * c * (q : G)⁻¹ * q := by group
        _ = c * q := by rw [h2]
    · intro hq
      apply Subtype.ext
      rw [hψQ]
      have h1 := (Subgroup.mem_centralizer_iff.mp (hDC hq)) c h.c_mem_D
      rw [← h1, mul_inv_cancel_right, mul_inv_cancel]
      rfl
  have hkerQ : Nat.card ψQ.ker = 81 := by
    have h1 : ψQ.ker.map Q.subtype = D := by
      ext u
      constructor
      · rintro ⟨q, hq, rfl⟩
        exact (hψQ1 q).mp hq
      · intro hu
        exact ⟨⟨u, hDQ hu⟩, (hψQ1 _).mpr hu, rfl⟩
    rw [← Subgroup.card_map_of_injective Q.subtype_injective, h1, h.card_D]
  have hQcard : Nat.card Q = 81 * 27 := by
    rw [KFacts.card_eq_card_ker_mul_card_range ψQ, hkerQ,
      MonoidHom.range_eq_top_of_surjective _ hψQsurj, Subgroup.card_top, h.card_inf]
  obtain ⟨x, hxL, hxN, hxo, hxfix⟩ := exists_orderOf_thirteen h
  have hx13 : x ^ 13 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hxL)
  have hxT : x ∈ Subgroup.normalizer (T : Set G) := mem_normalizer_transv hT hxc hxN
  have hxQ' : IsSylowOf 3 (Q.map (MulAut.conj x).toMonoidHom) T := by
    have h1 := IsSylowOf.map_conj hQsyl x
    have h2 : T.map (MulAut.conj x).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxT
    rwa [h2] at h1
  obtain ⟨k, hkT, hk⟩ := IsSylowOf.exists_mem_conj hQsyl hxQ'
  set y := k⁻¹ * x with hy
  have hyQ : y ∈ Subgroup.normalizer (Q : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro q hq
    have h1 : x * q * x⁻¹ ∈ Q.map (MulAut.conj x).toMonoidHom := ⟨q, hq, rfl⟩
    have h3 : y * q * y⁻¹ = k⁻¹ * (x * q * x⁻¹) * k := by rw [hy]; group
    rw [h3]
    exact (hk _).mp h1
  have hyE : y ∈ Subgroup.normalizer (E : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTE hkT)) hxN
  set τ : E →* E := (E.normalizerMonoidHom ⟨x, hxN⟩).toMonoidHom with hτ
  have hτapp : ∀ t : E, ((τ t : E) : G) = x * t * x⁻¹ := fun _ => rfl
  have hEcommG : ∀ u v : G, u ∈ E → v ∈ E → u * v = v * u := fun u v hu hv =>
    congrArg Subtype.val (hEe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hψy : ∀ q q' : Q, (q' : G) = y * q * y⁻¹ → ψQ q' = τ (ψQ q) := by
    intro q q' hq'
    apply Subtype.ext
    rw [hτapp]
    have htT : x * q * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hxT _).mp (hQT q.2)
    have h1 : ((ψ ⟨x * q * x⁻¹, htT⟩ : E) : G) = x * (ψQ q : G) * x⁻¹ :=
      psi_conj hψ hxc (Subgroup.inclusion hQT q) ⟨x * q * x⁻¹, htT⟩ rfl
    have h2 : (Subgroup.inclusion hQT q' : T) =
        (⟨k, hkT⟩ : T)⁻¹ * ⟨x * q * x⁻¹, htT⟩ * ⟨k, hkT⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv, hq', hy]
      group
    have h3 : ψQ q' = ψ (⟨k, hkT⟩ : T)⁻¹ * ψ ⟨x * q * x⁻¹, htT⟩ * ψ ⟨k, hkT⟩ := by
      rw [hψQdef, MonoidHom.comp_apply, h2, map_mul, map_mul]
    rw [h3, ← h1, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hEcommG _ _ (E.inv_mem (ψ ⟨k, hkT⟩).2) (ψ ⟨x * q * x⁻¹, htT⟩).2, inv_mul_cancel_right]
  have hτirr := irreducible_conj h.card_inf hx13 hxfix hxN
  have hψE : ∀ q : Q, (q : G) ∈ E → ψQ q = 1 := fun q hq => (hψQ1 q).mpr (hED hq)
  have hcentral : ∀ q z : Q, ψQ z = 1 → (q : G) * z * (q : G)⁻¹ * (z : G)⁻¹ ∈ E :=
    fun q z hz => commutator_mem_of_transv h hT (hQT q.2) ((hψQ1 z).mp hz)
  have hEcomm : ∀ e e' : E, e * e' = e' * e := fun e e' => hEe.1.is_comm.comm e e'
  have hEexp : ∀ e : E, e ^ 3 = 1 := fun e => Subtype.ext (by simpa using hEe.2 e e.2)
  obtain ⟨u, hu1, huE⟩ := exists_fixed_of_quotient (hED.trans hDQ) (hQT.trans hTE) hEcomm hEexp
    h.card_inf hQcard ψQ hψQsurj hψE hcentral hyQ hyE τ hψy hτirr haQ haN ha3
  set δ := (u : G)⁻¹ * (a * u * a⁻¹) with hδ
  have hauT : a * u * a⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp haT _).mp (hQT u.2)
  have haua : a * u * a⁻¹ = u * δ := by rw [hδ]; group
  have hψu : ((ψQ u : E) : G) ∈ Subgroup.zpowers d := by
    rw [← h.inf_centralizer_a hdL hA]
    refine ⟨(ψQ u).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : ((ψ ⟨a * u * a⁻¹, hauT⟩ : E) : G) = a * (ψQ u : G) * a⁻¹ :=
      psi_conj hψ hac (Subgroup.inclusion hQT u) ⟨a * u * a⁻¹, hauT⟩ rfl
    have hδT : δ ∈ T := hDT (hED huE)
    have h2 : (⟨a * u * a⁻¹, hauT⟩ : T) = Subgroup.inclusion hQT u * ⟨δ, hδT⟩ :=
      Subtype.ext haua
    have h3 : ψ ⟨δ, hδT⟩ = 1 := by
      apply Subtype.ext
      rw [hψ]
      have h4 := (Subgroup.mem_centralizer_iff.mp (hDC (hED huE))) c h.c_mem_D
      simp only
      rw [← h4, mul_inv_cancel_right, mul_inv_cancel]
      rfl
    rw [h2, map_mul, h3, mul_one] at h1
    have h5 : ((ψQ u : E) : G) = a * (ψQ u : G) * a⁻¹ := h1
    calc ((ψQ u : E) : G) * a = a * (ψQ u : G) * a⁻¹ * a := by rw [← h5]
      _ = a * (ψQ u : G) := by group
  have hNδ : δ * (a * δ * a⁻¹) * (a * (a * δ * a⁻¹) * a⁻¹) = 1 := by
    have h1 : a * (a * (a * (u : G) * a⁻¹) * a⁻¹) * a⁻¹ = u := by
      have ha3' : a * (a * a) = 1 := by rw [← pow_three]; exact ha3
      calc a * (a * (a * (u : G) * a⁻¹) * a⁻¹) * a⁻¹ = a * (a * a) * u * (a * (a * a))⁻¹ := by
            group
        _ = u := by rw [ha3', one_mul, inv_one, mul_one]
    have h2 : a * (a * (a * (u : G) * a⁻¹) * a⁻¹) * a⁻¹ =
        u * (δ * (a * δ * a⁻¹) * (a * (a * δ * a⁻¹) * a⁻¹)) := by
      rw [haua]
      have h3 : a * (u * δ) * a⁻¹ = u * δ * (a * δ * a⁻¹) := by
        rw [show a * (u * δ) * a⁻¹ = (a * u * a⁻¹) * (a * δ * a⁻¹) by group, haua]
      rw [h3]
      have h4 : a * (u * δ * (a * δ * a⁻¹)) * a⁻¹ =
          (a * u * a⁻¹) * (a * δ * a⁻¹) * (a * (a * δ * a⁻¹) * a⁻¹) := by group
      rw [h4, haua]
      group
    rw [h1] at h2
    exact (mul_eq_left.mp h2.symm)
  obtain ⟨z, hzE, hδz⟩ := exists_wreath_fix h97 h huE hNδ
  set v₀ := (u : G) * z with hv₀
  have hv₀a : v₀ * a * v₀⁻¹ = a := by
    have h1 : a * v₀ * a⁻¹ = v₀ := by
      calc a * v₀ * a⁻¹ = (a * u * a⁻¹) * (a * z * a⁻¹) := by rw [hv₀]; group
        _ = u * (z * (a * z * a⁻¹)⁻¹) * (a * z * a⁻¹) := by rw [haua, hδz]
        _ = v₀ := by rw [hv₀]; group
    have h2 : v₀ * a = a * v₀ := by
      calc v₀ * a = a * v₀ * a⁻¹ * a := by rw [h1]
        _ = a * v₀ := by group
    rw [h2, mul_inv_cancel_right]
  have hzc : z * c = c * z := (h.commute_c_of_mem_inf hzE)
  have hv₀E : ∀ e ∈ E, v₀ * e * v₀⁻¹ = e := by
    intro e he
    have h1 := ((hT u).mp (hQT u.2)).1 e he
    have h2 : z * e * z⁻¹ = e := by rw [hEcommG _ _ hzE he, mul_inv_cancel_right]
    calc v₀ * e * v₀⁻¹ = (u : G) * (z * e * z⁻¹) * (u : G)⁻¹ := by rw [hv₀]; group
      _ = e := by rw [h2, h1]
  have hv₀c : v₀ * c * v₀⁻¹ = (ψQ u : G) * c := by
    have h1 : z * c * z⁻¹ = c := by rw [hzc, mul_inv_cancel_right]
    calc v₀ * c * v₀⁻¹ = (u : G) * (z * c * z⁻¹) * (u : G)⁻¹ := by rw [hv₀]; group
      _ = (u : G) * c * (u : G)⁻¹ * c⁻¹ * c := by rw [h1]; group
      _ = (ψQ u : G) * c := by rw [hψQ]
  have hψu1 : ((ψQ u : E) : G) ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hψu
  have hdc : d * c = c * d := h.commute_c_of_mem_inf hdE
  rcases zpow_cases_of_pow_three (by rw [← hd3]; exact pow_orderOf_eq_one d) j with
    hj' | hj' | hj' <;> rw [hj'] at hj
  · exact (hψu1 hj.symm).elim
  · refine ⟨v₀, hv₀a, hv₀E d hdE, ?_⟩
    rw [hv₀c, ← hj, hdc]
  · refine ⟨v₀ * v₀, ?_, ?_, ?_⟩
    · calc v₀ * v₀ * a * (v₀ * v₀)⁻¹ = v₀ * (v₀ * a * v₀⁻¹) * v₀⁻¹ := by group
        _ = a := by rw [hv₀a, hv₀a]
    · calc v₀ * v₀ * d * (v₀ * v₀)⁻¹ = v₀ * (v₀ * d * v₀⁻¹) * v₀⁻¹ := by group
        _ = d := by rw [hv₀E d hdE, hv₀E d hdE]
    · have hd2 : (d ^ 2) * (d ^ 2) = d := by
        rw [← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ,
          (by rw [← hd3]; exact pow_orderOf_eq_one d : d ^ 3 = 1), one_mul]
      have hd2E : d ^ 2 ∈ E := Subgroup.pow_mem _ hdE 2
      calc v₀ * v₀ * c * (v₀ * v₀)⁻¹ = v₀ * (v₀ * c * v₀⁻¹) * v₀⁻¹ := by group
        _ = v₀ * (d ^ 2 * c) * v₀⁻¹ := by rw [hv₀c, ← hj]
        _ = (v₀ * d ^ 2 * v₀⁻¹) * (v₀ * c * v₀⁻¹) := by group
        _ = d ^ 2 * (d ^ 2 * c) := by rw [hv₀E _ hd2E, hv₀c, ← hj]
        _ = c * d := by rw [← mul_assoc, hd2, hdc]

end Std

end Item107Proof

end CFSG.RankThree.PartTwo.Sec10
