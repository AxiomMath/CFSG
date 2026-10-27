module

public import CFSG.Quasithin.Background.ElemTwoOdd
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7One
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem18Stmts
public import CFSG.Quasithin.H13.A6S1372L24a
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem18R

section Lift

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem exists_lift (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X} [K.Normal]
    (hK : IsPGroup 2 K) {B : Subgroup (X ⧸ K)} (hB : IsElemAbelian p B) {d : ℕ}
    (hBd : Nat.card B = p ^ d) :
    ∃ S : Subgroup X, IsElemAbelian p S ∧ Nat.card S = p ^ d := by
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' K with hπ
  set Y := B.comap π with hY
  have hKY : K ≤ Y := fun k hk => by
    show π k ∈ B
    have h1 : π k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    rw [h1]
    exact B.one_mem
  have hYmap : Y.map π = B := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective K) B
  have hYker : Y ⊓ π.ker = K := by
    rw [hπ, QuotientGroup.ker_mk']
    exact inf_eq_right.mpr hKY
  have hcardY := B1More.card_map_mul_card_inf_ker Y π
  rw [hYmap, hYker, hBd] at hcardY
  have hNcard : Nat.card ↥(K.subgroupOf Y) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKY).toEquiv
  have hNindex : (K.subgroupOf Y).index = p ^ d := by
    have h1 := (K.subgroupOf Y).card_mul_index
    rw [hNcard, ← hcardY] at h1
    have hK0 : 0 < Nat.card K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hK0 (by rw [h1, mul_comm])
  obtain ⟨a, ha⟩ := hK.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥(K.subgroupOf Y)) (K.subgroupOf Y).index := by
    rw [hNcard, ha, hNindex]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = p ^ d := by
    have h1 := hH.card_mul_card
    rw [hNcard, ← hcardY] at h1
    have hK0 : 0 < Nat.card K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hK0 (by rw [h1, mul_comm])
  have hHN : ∀ h ∈ H, (h : X) ∈ K → h = 1 := by
    intro h hh hhK
    have h1 : h ∈ K.subgroupOf Y ⊓ H := ⟨Subgroup.mem_subgroupOf.mpr hhK, hh⟩
    rw [hH.isCompl.inf_eq_bot, Subgroup.mem_bot] at h1
    exact h1
  have hinj : ∀ h₁ ∈ H, ∀ h₂ ∈ H, π h₁ = π h₂ → h₁ = h₂ := by
    intro h₁ hh₁ h₂ hh₂ he
    have h3 : ((h₁⁻¹ * h₂ : ↥Y) : X) ∈ K := by
      have h5 : π ((h₁ : X)⁻¹ * h₂) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
      have h6 := (QuotientGroup.eq_one_iff _).mp h5
      simpa using h6
    have h4 := hHN _ (H.mul_mem (H.inv_mem hh₁) hh₂) h3
    exact (inv_mul_eq_one.mp h4)
  refine ⟨H.map Y.subtype, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro ⟨_, ⟨h₁, hh₁, rfl⟩⟩ ⟨_, ⟨h₂, hh₂, rfl⟩⟩
    apply Subtype.ext
    show (h₁ : X) * h₂ = h₂ * h₁
    have h3 : π (h₁ * h₂) = π (h₂ * h₁) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hB.1.is_comm.comm ⟨π h₁, h₁.2⟩ ⟨π h₂, h₂.2⟩)
    have := hinj _ (H.mul_mem hh₁ hh₂) _ (H.mul_mem hh₂ hh₁) h3
    exact congrArg Subtype.val this
  · rintro _ ⟨h, hh, rfl⟩
    have h3 : π ((h : X) ^ p) = π 1 := by
      rw [map_pow, map_one]
      exact hB.2 _ h.2
    have := hinj (h ^ p) (H.pow_mem hh p) 1 H.one_mem (by simpa using h3)
    simpa using congrArg Subtype.val this
  · rw [Subgroup.card_map_of_injective Y.subtype_injective, hHcard]

end Lift

section Solvable

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem card_le_four_of_solvable [Group.IsSolvable X] (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : ∀ q : ℕ, q.Prime → q ∣ Nat.card X → q = 2 ∨ q = p)
    (hrank : ∀ S : Subgroup X, IsElemAbelian p S → ∀ d, Nat.card S = p ^ d → d ≤ 2)
    {E : Subgroup X} (hE2 : ∀ e ∈ E, e * e = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEO : E ⊓ CFSG.pCore 2 X = ⊥) : Nat.card E ≤ 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := CFSG.pCore 2 X with hKdef
  have hK2 : IsPGroup 2 K := CFSG.pCore_isPGroup
  set π := QuotientGroup.mk' K with hπ
  have hO2 : CFSG.pCore 2 (X ⧸ K) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hpp : CFSG.pPrimeCore p (X ⧸ K) = ⊥ := by
    have : (CFSG.pPrimeCore p (X ⧸ K)).Normal := CFSG.pPrimeCore_normal
    have hcop := CFSG.pPrimeCore_coprime_card (p := p) (G := X ⧸ K)
    have hdvd : Nat.card (CFSG.pPrimeCore p (X ⧸ K)) ∣ Nat.card X :=
      (Subgroup.card_subgroup_dvd_card _).trans
        (Subgroup.card_quotient_dvd_card K)
    have h2 : IsPGroup 2 (CFSG.pPrimeCore p (X ⧸ K)) := by
      apply IsPGroup.of_card (n := (Nat.card (CFSG.pPrimeCore p (X ⧸ K))).primeFactorsList.length)
      refine Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {q} hq hqd => ?_
      rcases hX q hq (hqd.trans hdvd) with h | h
      · exact h
      · exfalso
        rw [h] at hqd
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop hqd
    rw [eq_bot_iff, ← hO2]
    exact le_sSup ⟨inferInstance, h2⟩
  have hF : CFSG.fittingSubgroup (X ⧸ K) = CFSG.pCore p (X ⧸ K) :=
    CFSG.Fitting_eq_pcore (X ⧸ K) p hpp
  have hC : Subgroup.centralizer (CFSG.pCore p (X ⧸ K) : Set (X ⧸ K)) ≤
      CFSG.pCore p (X ⧸ K) := by
    rw [← hF]
    exact CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable inferInstance
  set Eb := E.map π with hEb
  have hEbcard : Nat.card Eb = Nat.card E := by
    have h := B1More.card_map_mul_card_inf_ker E π
    rw [hπ, QuotientGroup.ker_mk', hEO, Subgroup.card_bot, mul_one] at h
    exact h
  have hEb2 : ∀ e ∈ Eb, e * e = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hE2 a ha, map_one]
  have hEbc : ∀ a ∈ Eb, ∀ b ∈ Eb, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hEc a ha b hb]
  have hfaith : ∀ e ∈ Eb, (∀ z ∈ CFSG.pCore p (X ⧸ K), e * z * e⁻¹ = z) → e = 1 := by
    intro e he h1
    have heC : e ∈ Subgroup.centralizer (CFSG.pCore p (X ⧸ K) : Set (X ⧸ K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      calc z * e = (e * z * e⁻¹) * e := by rw [h1 z hz]
        _ = e * z := by group
    exact ElemTwoOdd.eq_one_of_mul_self (hp.odd_of_ne_two hp2) CFSG.pCore_isPGroup (hC heC)
      (hEb2 e he)
  obtain ⟨B, d, -, hB, hBd, hEd⟩ := ElemTwoOdd.exists_elemAbelian_of_faithful hp hp2
    (P := CFSG.pCore p (X ⧸ K)) (E := Eb) CFSG.pCore_isPGroup
    (fun e _ => Subgroup.mem_normalizer_iff.mpr fun z => ⟨fun hz =>
      (CFSG.pCore_normal (p := p) (G := X ⧸ K)).conj_mem z hz e, fun hz => by
        have := (CFSG.pCore_normal (p := p) (G := X ⧸ K)).conj_mem _ hz e⁻¹
        simpa [mul_assoc] using this⟩)
    hEbc hEb2 hfaith
  obtain ⟨S, hS, hSd⟩ := exists_lift hp hp2 hK2 hB hBd
  have hd := hrank S hS d hSd
  calc Nat.card E = Nat.card Eb := hEbcard.symm
    _ ≤ 2 ^ d := hEd
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hd
    _ = 4 := by norm_num

end Solvable

section L24

variable {G : Type} [Group G] [Finite G]

theorem card_le_four_of_L24 {H W : Subgroup G} (hWH : W ≤ H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) (hred : IsPrimeReduced 2 (W.subgroupOf H))
    (hO2 : pCoreOf 2 H ≤ Subgroup.centralizer (W : Set G))
    (hHC : ¬ H ≤ Subgroup.centralizer (W : Set G))
    (hLie : LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 2)
    {E : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian 2 E)
    (hEC : E ⊓ Subgroup.centralizer (W : Set G) = ⊥) : Nat.card E ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set P := H ⊓ Subgroup.centralizer (W : Set G) with hPdef
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh, B6.le_normalizer_centralizer hHW hh⟩
  have hPconj : ∀ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ P := fun h hh x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHP hh) x).mp hx
  obtain ⟨-, -, hD⟩ := (isPrimeReduced_iff_forall 2).mp hred
  have hcW : ∀ h : ↥H, h ∈ Subgroup.centralizer ((W.subgroupOf H : Subgroup ↥H) : Set ↥H) →
      (h : G) ∈ Subgroup.centralizer (W : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have := Subgroup.mem_centralizer_iff.mp hh ⟨w, hWH hw⟩ (Subgroup.mem_subgroupOf.mpr hw)
    exact congrArg Subtype.val this
  have hcW' : ∀ h : ↥H, (h : G) ∈ Subgroup.centralizer (W : Set G) →
      h ∈ Subgroup.centralizer ((W.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro h hh
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => Subtype.ext ?_
    push_cast
    exact (Subgroup.mem_centralizer_iff.mp hh) w (Subgroup.mem_subgroupOf.mp hw)
  obtain ⟨e₁⟩ : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) := by
    rcases hLie with ⟨-, -, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
        (Or.inl (by rw [hF]; norm_num))
      exact ⟨e.trans e5⟩
    all_goals exact absurd h0 (by norm_num)
  set α : ↥K →* alternatingGroup (Fin 5) :=
    e₁.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hα
  have hαs : Function.Surjective α := e₁.surjective.comp (QuotientGroup.mk'_surjective _)
  have hαker : ∀ k : ↥K, α k = 1 ↔ k ∈ CFSG.pCore 2 ↥K := by
    intro k
    rw [hα, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hO2K : ∀ k : ↥K, k ∈ CFSG.pCore 2 ↥K → (k : G) ∈ P := by
    intro k hk
    have h1 : (k : G) ∈ pCoreOf 2 K := by
      exact ⟨k, hk, rfl⟩
    have h2 : pCoreOf 2 K ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
        (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact ⟨hKH k.2, hO2 (h2 h1)⟩
  have hKP : ¬ K ≤ P := by
    intro hKP
    apply hHC
    have hall := hD ⊤ inferInstance fun d _ => by
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H d.2
      refine ⟨k, hcW' _ ?_⟩
      push_cast
      exact (hKP hk).2
    exact fun h hh => hcW ⟨h, hh⟩ (hall (Subgroup.mem_top _))
  have hαP : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P := by
    intro k
    refine ⟨fun h1 => hO2K k ((hαker k).mp h1), fun hk => ?_⟩
    have hPn : (P.subgroupOf K).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      push_cast
      exact hPconj g (hKH g.2) x hx⟩
    have hQn : ((P.subgroupOf K).map α).Normal := hPn.map α hαs
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 5) (by simp)
        (N := (P.subgroupOf K).map α) with h | h
    · have : α k ∈ (P.subgroupOf K).map α := ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      apply hKP
      intro x hx
      have : α ⟨x, hx⟩ ∈ (P.subgroupOf K).map α := by rw [h]; trivial
      obtain ⟨y, hy, hyx⟩ := this
      have h2 : α (y⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
      have h3 := hO2K _ ((hαker _).mp h2)
      have h4 : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥K) : G) := by push_cast; group
      rw [h4]
      exact P.mul_mem (Subgroup.mem_subgroupOf.mp hy) h3
  let D : Subgroup ↥H :=
    { carrier := {h | ∀ k ∈ K, (h : G) * k * (h : G)⁻¹ * k⁻¹ ∈ P}
      one_mem' := fun k _ => by simp [P.one_mem]
      mul_mem' := fun {a b} ha hb k hk => by
        have e1 : ((a * b : ↥H) : G) * k * ((a * b : ↥H) : G)⁻¹ * k⁻¹ =
            (a : G) * ((b : G) * k * (b : G)⁻¹ * k⁻¹) * (a : G)⁻¹ *
              ((a : G) * k * (a : G)⁻¹ * k⁻¹) := by
          push_cast
          group
        rw [e1]
        exact P.mul_mem (hPconj a a.2 _ (hb k hk)) (ha k hk)
      inv_mem' := fun {a} ha k hk => by
        have e1 : ((a⁻¹ : ↥H) : G) * k * ((a⁻¹ : ↥H) : G)⁻¹ * k⁻¹ =
            (a : G)⁻¹ * ((a : G) * k * (a : G)⁻¹ * k⁻¹)⁻¹ * (a : G)⁻¹⁻¹ := by
          push_cast
          group
        rw [e1]
        exact hPconj _ (H.inv_mem a.2) _ (P.inv_mem (ha k hk)) }
  have hDn : D.Normal := ⟨fun d hd g k hk => by
    have hk' : (g : G)⁻¹ * k * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hHK (H.inv_mem g.2)) k).mp hk
      simpa using this
    have h1 := hPconj g g.2 _ (hd _ hk')
    convert h1 using 1
    push_cast
    group⟩
  have hD2 : ∀ d ∈ D, ∃ a : ℕ, d ^ 2 ^ a ∈
      Subgroup.centralizer ((W.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro d hd
    obtain ⟨a, ha⟩ := exists_pow_mem_oTwoUpper H d.2
    refine ⟨a, hcW' _ ?_⟩
    have hdD : d ^ 2 ^ a ∈ D := D.pow_mem hd _
    set x : ↥K := ⟨(d : G) ^ 2 ^ a, ha⟩ with hx
    have hxc : α x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := hαs y
      have h1 : α (x * k * x⁻¹ * k⁻¹) = 1 := by
        rw [hαP]
        have := hdD k k.2
        push_cast at this ⊢
        exact this
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hxc
    have hxP := ((hαP x).mp hxc).2
    push_cast
    exact hxP
  have hDC := hD D hDn hD2
  have hfaith : ∀ e ∈ E, (∀ k ∈ K, e * k * e⁻¹ * k⁻¹ ∈ P) → e ∈ P := fun e he hk =>
    ⟨hEH he, hcW ⟨e, hEH he⟩ (hDC (show (⟨e, hEH he⟩ : ↥H) ∈ D from hk))⟩
  have hsq : ∀ e ∈ E, e * e ∈ P := by
    intro e he
    rw [← pow_two, hE.2 e he]
    exact P.one_mem
  have h4 := A6.A6L24.relIndex_le_four (hKH.trans hHP) (hEH.trans hHP) (hEH.trans hHK) hαs hαP
    hfaith hsq
  have hPE : P ⊓ E = ⊥ := by
    rw [eq_bot_iff, ← hEC]
    exact fun x hx => ⟨hx.2, hx.1.2⟩
  rw [hPE, Subgroup.relIndex_bot_left] at h4
  exact h4

end L24

end Lem18R

open Lem18R

theorem lem12218TwoRank_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h323 : Stmt3_2_3) (h1227 : Stmt12_2_7) : Lem12218TwoRank := by
  classical
  intro G _ _ T L V H hH hCZ hHs E hEH hE hEC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hred, -, hO2, -⟩ := stmt12_2_7_one h331 h1222 (stmt12_2_6_of h1222 h323) hH hCZ hHs
  have hZT : quasithinOmegaOneCenter T ≤ T := (Subgroup.closure_le T).mpr fun z hz => hz.1.1
  have hWH : VZ T H ≤ H := conjClosure_le fun h hh z hz =>
    H.mul_mem (H.mul_mem hh (hHs.1.1 (hZT hz))) (H.inv_mem hh)
  have hHW : H ≤ Subgroup.normalizer (VZ T H : Set G) := le_normalizer_conjClosure _ H
  have hO2' : pCoreOf 2 H ≤ Subgroup.centralizer (VZ T H : Set G) := fun x hx => (hO2 hx).2
  by_cases hsolv : Group.IsSolvable ↥H
  · obtain ⟨p, hp, hp2, hX⟩ :=
      (Lem7.minParabolic h331 hH hHs).subgroupOf.exists_odd_prime_of_solvable hsolv
    have hrk : CFSG.Open.pRank p (⊤ : Subgroup ↥H) ≤ 2 :=
      CFSG.SectionRank.isStronglyQuasithin_iff.mp
        (isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank hH.qtke.2.2 hHs.1.2) p hp hp2
    have hrank : ∀ S : Subgroup ↥H, IsElemAbelian p S → ∀ d, Nat.card S = p ^ d → d ≤ 2 :=
      fun S hS d hd => (CFSG.Quasithin.le_pRank hp le_top hS hd).trans hrk
    set E' := E.subgroupOf H with hE'
    have hE'c : Nat.card E' = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
    rw [← hE'c]
    refine card_le_four_of_solvable hp hp2 hX hrank (fun e he => ?_) (fun a ha b hb => ?_) ?_
    · apply Subtype.ext
      have h1 := hE.2 _ (Subgroup.mem_subgroupOf.mp he)
      push_cast
      rw [← pow_two]
      exact h1
    · apply Subtype.ext
      push_cast
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨a, Subgroup.mem_subgroupOf.mp ha⟩
        ⟨b, Subgroup.mem_subgroupOf.mp hb⟩)
    · rw [eq_bot_iff]
      rintro x ⟨hxE, hxO⟩
      have h1 : (x : G) ∈ E ⊓ Subgroup.centralizer (VZ T H : Set G) :=
        ⟨Subgroup.mem_subgroupOf.mp hxE, hO2' ⟨x, hxO, rfl⟩⟩
      rw [hEC, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  · exact card_le_four_of_L24 hWH hHW hred hO2' (Lem7.not_le_centralizer_VZ hCZ hHs)
      ((h1227 G T L V H hH hCZ hHs).2 hsolv).1 hEH hE hEC

end CFSG.Quasithin.H13
