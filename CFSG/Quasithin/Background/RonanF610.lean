module

public import CFSG.Quasithin.Background.RonanF610Sylow
public import CFSG.Quasithin.Background.RonanF65
public import CFSG.Quasithin.Background.F6ComponentBound

public section

universe u

namespace CFSG.Quasithin.RonanF610

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6

variable {D : Type*} [Group D] [Finite D]

theorem le_of_normal_of_inf_le {G₁ G₂ N : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂)
    [N.Normal] (hT : G₁ ⊓ G₂ ≤ N) : G₁ ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : G₁ ⊓ G₂ ≤ G₁ ⊓ N := le_inf inf_le_left hT
  have hMG : G₁ ⊓ N ≤ G₁ := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (G₁ ⊓ G₂) (G₁ ⊓ N) G₁ hTM hMG
  rw [h.relIndex_inf_left] at hmul
  by_cases h1 : (G₁ ⊓ N).relIndex G₁ = 1
  · exact (Subgroup.relIndex_eq_one.mp h1).trans inf_le_right
  · exfalso
    have hd : (G₁ ⊓ N).relIndex G₁ ∣ 3 := Dvd.intro_left _ hmul
    have h3 : (G₁ ⊓ N).relIndex G₁ = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h' | h'
      · exact absurd h' h1
      · exact h'
    have h2 : (G₁ ⊓ G₂).relIndex (G₁ ⊓ N) = 1 := by
      rw [h3] at hmul
      omega
    have hMeq : G₁ ⊓ N = G₁ ⊓ G₂ := le_antisymm (Subgroup.relIndex_eq_one.mp h2) hTM
    have hNM : G₁ ≤ Subgroup.normalizer ((G₁ ⊓ N : Subgroup D) : Set D) :=
      F6.le_normalizer_inf_of_normal G₁
    rw [hMeq] at hNM
    have hle : G₁ ⊓ G₂ ≤ pCoreOf 2 G₁ :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left hNM h.isPGroup_inf
    have hc := Subgroup.card_le_of_le hle
    have := GoldAmN.card_inf_eq_two_mul_left h
    have hpos : 0 < Nat.card ↥(pCoreOf 2 G₁) := Nat.card_pos
    omega

theorem eq_top_of_normal_of_inf_le {G₁ G₂ N : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂)
    [N.Normal] (hT : G₁ ⊓ G₂ ≤ N) : N = ⊤ := by
  have h₁ := le_of_normal_of_inf_le h hT
  have h₂ := le_of_normal_of_inf_le (N := N) h.symm (by rw [inf_comm]; exact hT)
  rw [eq_top_iff, ← h.gen]
  exact sup_le h₁ h₂

theorem card_inf_bound_oriented {H₁ H₂ : Subgroup D} (h : IsGoldschmidtAmalgam H₁ H₂)
    (hc : IsGoldCaseOrientedCat H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) ≤ 128 ∧
      (Nat.card ↥(H₁ ⊓ H₂) = 128 → Nat.card ↥(centerOf (H₁ ⊓ H₂)) ≤ 2) := by
  have hG := h.toIsGoldschmidtTriple
  rcases hc with hc | hc | hc | hc | hc | hc
  · rw [hc.card_inf]; norm_num
  · rw [hc.card_inf]; norm_num
  · rw [hc.card_inf]; norm_num
  · rw [hc.card_inf]; norm_num
  · rw [hc.card_inf]; norm_num
  · have hC := RonanF65.charTwo_of_isGoldCaseVICat h hc
    rcases hc with hc | hc | hc | hc | hc | hc
    · rw [hc.card_inf hG]; norm_num
    · rw [hc.card_inf hG]; norm_num
    · rw [hc.card_inf hG]; norm_num
    · rw [hc.card_inf hG]; norm_num
    · rw [hc.card_inf hG]; norm_num
    · refine ⟨?_, fun _ => ?_⟩
      · rw [GoldAmN.card_inf_eq_two_mul_right hG, hc.2.2.2.2.2.2.2]
        norm_num
      · calc Nat.card ↥(centerOf (H₁ ⊓ H₂)) ≤ Nat.card ↥(centerOf (pCoreOf 2 H₁)) :=
            Subgroup.card_le_of_le (centerOf_inf_le_centerOf_pCoreOf hG hC.1)
          _ = 2 := hc.2.2.2.2.2.2.1

theorem card_inf_bound (hlist : GoldschmidtS3ListCat.{u}) {D : Type u} [Group D] [Finite D]
    {H₁ H₂ : Subgroup D} (h : IsGoldschmidtAmalgam H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) ≤ 128 ∧
      (Nat.card ↥(H₁ ⊓ H₂) = 128 → Nat.card ↥(centerOf (H₁ ⊓ H₂)) ≤ 2) := by
  rcases hlist D H₁ H₂ h with hc | hc
  · exact card_inf_bound_oriented h hc
  · have := card_inf_bound_oriented (GoldAmN.amalgam_symm h) hc
    rwa [inf_comm H₂ H₁] at this

theorem le_centralizer_self_of_sq {A : Subgroup D} (hA : ∀ x ∈ A, x ^ 2 = 1) :
    A ≤ Subgroup.centralizer (A : Set D) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 : (y * x) * (y * x) = 1 := by rw [← pow_two]; exact hA _ (A.mul_mem hy hx)
  have h2 : x * x = 1 := by rw [← pow_two]; exact hA _ hx
  have h3 : y * y = 1 := by rw [← pow_two]; exact hA _ hy
  have hxi : x⁻¹ = x := (eq_inv_of_mul_eq_one_left h2).symm
  have hyi : y⁻¹ = y := (eq_inv_of_mul_eq_one_left h3).symm
  have hyxi : (y * x)⁻¹ = y * x := (eq_inv_of_mul_eq_one_left h1).symm
  calc y * x = (y * x)⁻¹ := hyxi.symm
    _ = x⁻¹ * y⁻¹ := mul_inv_rev y x
    _ = x * y := by rw [hxi, hyi]

theorem false_of_three_commuting {T N₀ S₁ S₂ S₃ : Subgroup D} [N₀.Normal]
    (hPT : S₁ ⊔ S₂ ⊔ S₃ ≤ T) (hPN : S₁ ⊔ S₂ ⊔ S₃ ≤ N₀) (hTN : ¬ T ≤ N₀)
    (h64 : 64 ≤ Nat.card ↥(S₁ ⊔ S₂ ⊔ S₃))
    (hsq : Nat.card ↥(S₁ ⊔ S₂ ⊔ S₃) ≤ 64 →
      (∀ x ∈ S₁, x ^ 2 = 1) ∧ (∀ x ∈ S₂, x ^ 2 = 1) ∧ (∀ x ∈ S₃, x ^ 2 = 1))
    (c₁₂ : S₁ ≤ Subgroup.centralizer (S₂ : Set D)) (c₁₃ : S₁ ≤ Subgroup.centralizer (S₃ : Set D))
    (c₂₃ : S₂ ≤ Subgroup.centralizer (S₃ : Set D)) (h128 : Nat.card ↥T ≤ 128)
    (hZ : Nat.card ↥T = 128 → Nat.card ↥(centerOf T) ≤ 2) : False := by
  set P := S₁ ⊔ S₂ ⊔ S₃ with hP
  obtain ⟨t, htT, htN₀⟩ := SetLike.not_le_iff_exists.mp hTN
  have hrel : (T ⊓ N₀).relIndex T ≠ 1 := fun h1 =>
    hTN ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_right)
  have hrel0 : (T ⊓ N₀).relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmulT := Subgroup.relIndex_mul_card (H := T ⊓ N₀) (K := T)
  have e : T ⊓ N₀ ⊓ T = T ⊓ N₀ := inf_eq_left.mpr inf_le_left
  rw [e] at hmulT
  have hPle : Nat.card ↥P ≤ Nat.card ↥(T ⊓ N₀) := Subgroup.card_le_of_le (le_inf hPT hPN)
  have h2 : 2 * Nat.card ↥(T ⊓ N₀) ≤ Nat.card ↥T := by
    rw [← hmulT]
    exact Nat.mul_le_mul_right _ (by omega)
  have hTN64 : Nat.card ↥(T ⊓ N₀) = 64 := by omega
  have hT128 : Nat.card ↥T = 128 := by omega
  have hPcard : Nat.card ↥P = 64 := by omega
  have hPeq : P = T ⊓ N₀ := Subgroup.eq_of_le_of_card_ge (le_inf hPT hPN) (by omega)
  have hidx2 : P.relIndex T = 2 := by
    rw [hPeq]
    have h' : (T ⊓ N₀).relIndex T * 64 = 128 := by rw [← hTN64, hmulT, hT128]
    omega
  obtain ⟨hsq₁, hsq₂, hsq₃⟩ := hsq hPcard.le
  have c₂₁ : S₂ ≤ Subgroup.centralizer (S₁ : Set D) := Subgroup.le_centralizer_iff.mp c₁₂
  have c₃₁ : S₃ ≤ Subgroup.centralizer (S₁ : Set D) := Subgroup.le_centralizer_iff.mp c₁₃
  have c₃₂ : S₃ ≤ Subgroup.centralizer (S₂ : Set D) := Subgroup.le_centralizer_iff.mp c₂₃
  have hPS₁ : P ≤ Subgroup.centralizer (S₁ : Set D) :=
    sup_le (sup_le (le_centralizer_self_of_sq hsq₁) c₂₁) c₃₁
  have hPS₂ : P ≤ Subgroup.centralizer (S₂ : Set D) :=
    sup_le (sup_le c₁₂ (le_centralizer_self_of_sq hsq₂)) c₃₂
  have hPS₃ : P ≤ Subgroup.centralizer (S₃ : Set D) :=
    sup_le (sup_le c₁₃ c₂₃) (le_centralizer_self_of_sq hsq₃)
  have hPab : P ≤ Subgroup.centralizer (P : Set D) :=
    sup_le (sup_le (Subgroup.le_centralizer_iff.mp hPS₁) (Subgroup.le_centralizer_iff.mp hPS₂))
      (Subgroup.le_centralizer_iff.mp hPS₃)
  have hab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hPab hx) y hy).symm
  have hPsq : ∀ x ∈ P, x ^ 2 = 1 := by
    let E : Subgroup D :=
      { carrier := {x | x ∈ P ∧ x ^ 2 = 1}
        mul_mem' := fun {a b} ha hb => ⟨P.mul_mem ha.1 hb.1, by
          rw [Commute.mul_pow (hab a ha.1 b hb.1), ha.2, hb.2, one_mul]⟩
        one_mem' := ⟨P.one_mem, one_pow 2⟩
        inv_mem' := fun {a} ha => ⟨P.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
    have hSE : ∀ {A : Subgroup D}, A ≤ P → (∀ x ∈ A, x ^ 2 = 1) → A ≤ E :=
      fun hAP hA x hx => ⟨hAP hx, hA x hx⟩
    have hPE : P ≤ E := sup_le (sup_le (hSE (le_sup_left.trans le_sup_left) hsq₁)
      (hSE (le_sup_right.trans le_sup_left) hsq₂)) (hSE le_sup_right hsq₃)
    exact fun x hx => (hPE hx).2
  have hTNP : T ≤ Subgroup.normalizer (P : Set D) := by
    rw [hPeq]
    exact F6.le_normalizer_inf_of_normal T
  have ht2 : t ^ 2 ∈ P := GoldAmN.sq_mem_of_relIndex_two hPT hTNP hidx2 htT
  have h8 := eight_le_card_inf_centralizer hab hPsq hPcard (hTNP htT) ht2
  have htP : t ∉ P := fun h => htN₀ (hPN h)
  have hZT : P ⊓ Subgroup.centralizer ({t} : Set D) ≤ centerOf T := by
    intro x hx
    obtain ⟨hxP, hxt⟩ := Subgroup.mem_inf.mp hx
    have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
    refine ⟨hPT hxP, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    by_cases hyP : y ∈ P
    · exact hab y hyP x hxP
    · have hidx' : (P.subgroupOf T).index = 2 := hidx2
      have hmem : (⟨t, htT⟩ : ↥T)⁻¹ * ⟨y, hy⟩ ∈ P.subgroupOf T := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx']
        refine iff_of_false (fun h' => htP ?_) (fun h' => hyP h')
        have := P.inv_mem (Subgroup.mem_subgroupOf.mp h')
        simpa using this
      have hty : t⁻¹ * y ∈ P := Subgroup.mem_subgroupOf.mp hmem
      calc y * x = t * (t⁻¹ * y * x) := by group
        _ = t * (x * (t⁻¹ * y)) := by rw [hab _ hty x hxP]
        _ = x * t * (t⁻¹ * y) := by rw [hxt']; group
        _ = x * y := by group
  have := Subgroup.card_le_of_le hZT
  have := hZ hT128
  omega

omit [Finite D] in
theorem mem_map_conj {K : Subgroup D} {g y : D} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_le_normalizer {K : Subgroup D} (hK : CFSG.IsComponent K) (g : D) :
    K.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (K : Set D) := by
  have hc := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK
  rcases CFSG.LocalCores.distinct_components_commute hc hK with heq | hbot
  · rw [heq]
    exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot).trans
      (Subgroup.centralizer_le_normalizer _)

theorem map_conj_le_normalCore {K : Subgroup D} (hK : CFSG.IsComponent K) (g : D) :
    K.map (MulAut.conj g).toMonoidHom ≤ (Subgroup.normalizer (K : Set D)).normalCore := by
  intro x hx b
  refine map_conj_le_normalizer hK (b * g) ?_
  rw [mem_map_conj] at hx ⊢
  have e : (b * g)⁻¹ * (b * x * b⁻¹) * (b * g) = g⁻¹ * x * g := by group
  rw [e]
  exact hx

theorem index_normalizer_le_two_of_amalgam (hlist : GoldschmidtS3ListCat.{u}) {D : Type u}
    [Group D] [Finite D] {G₁ G₂ : Subgroup D} (h : IsGoldschmidtAmalgam G₁ G₂)
    {K : Subgroup D} (hK : CFSG.IsComponent K) :
    (Subgroup.normalizer (K : Set D)).index ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG := h.toIsGoldschmidtTriple
  by_contra hidx
  have hcard : 2 < Nat.card (D ⧸ Subgroup.normalizer (K : Set D)) := not_le.mp hidx
  obtain ⟨q₂, hq₂⟩ : ∃ q : D ⧸ Subgroup.normalizer (K : Set D),
      q ≠ (QuotientGroup.mk 1 : D ⧸ Subgroup.normalizer (K : Set D)) := by
    by_contra hall
    push Not at hall
    have : Nat.card (D ⧸ Subgroup.normalizer (K : Set D)) ≤ 1 :=
      Finite.card_le_one_iff_subsingleton.mpr ⟨fun a b => (hall a).trans (hall b).symm⟩
    omega
  obtain ⟨q₃, hq₃, hq₃'⟩ : ∃ q : D ⧸ Subgroup.normalizer (K : Set D),
      q ≠ (QuotientGroup.mk 1 : D ⧸ Subgroup.normalizer (K : Set D)) ∧ q ≠ q₂ := by
    by_contra hall
    push Not at hall
    have hsurj : Function.Surjective (fun b : Bool =>
        if b then (QuotientGroup.mk 1 : D ⧸ Subgroup.normalizer (K : Set D)) else q₂) := by
      intro q
      by_cases hq : q = QuotientGroup.mk 1
      · exact ⟨true, by simp [hq]⟩
      · exact ⟨false, by simp [hall q hq]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    have h2 : Nat.card Bool = 2 := by simp
    omega
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
  obtain ⟨g₃, rfl⟩ := QuotientGroup.mk_surjective q₃
  let c : D → Subgroup D := fun g => K.map (MulAut.conj g).toMonoidHom
  have hc : ∀ g, CFSG.IsComponent (c g) := fun g =>
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hK
  have hne : ∀ g h : D, (QuotientGroup.mk g : D ⧸ Subgroup.normalizer (K : Set D)) ≠
      QuotientGroup.mk h → c g ≠ c h :=
    fun g h hgh hc' => hgh (QuotientGroup.eq.mpr (F6.mem_normalizer_of_map_conj_eq hc'))
  have hle : ∀ g h : D, c g ≠ c h → c g ≤ Subgroup.centralizer (c h : Set D) := by
    intro g h hgh
    rcases CFSG.LocalCores.distinct_components_commute (hc g) (hc h) with heq | hbot
    · exact absurd heq hgh
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  have h12 := hne 1 g₂ (Ne.symm hq₂)
  have h13 := hne 1 g₃ (Ne.symm hq₃)
  have h23 := hne g₂ g₃ (Ne.symm hq₃')
  have hTsyl : IsSylowIn 2 (G₁ ⊓ G₂) ⊤ := isSylowTwoOf_inf_top hG
  have hS : ∀ g, IsSylowIn 2 (G₁ ⊓ G₂ ⊓ c g) (c g) := fun g =>
    isSylowIn_inf_of_isSubnormal (isSubnormal_top_of_isSubnormal (hc g).2) hTsyl
  have h4 : ∀ g, 4 ≤ (centerOf (c g)).relIndex (G₁ ⊓ G₂ ⊓ c g) := fun g =>
    four_le_relIndex_centerOf (hc g).1 (hS g)
  have hS4 : ∀ g, 4 ≤ Nat.card ↥(G₁ ⊓ G₂ ⊓ c g) := fun g =>
    (h4 g).trans (relIndex_le_card _ _)
  have hP1 : 16 * Nat.card ↥(G₁ ⊓ G₂ ⊓ c 1) ≤
      Nat.card ↥(G₁ ⊓ G₂ ⊓ c 1 ⊔ G₁ ⊓ G₂ ⊓ c g₂ ⊔ G₁ ⊓ G₂ ⊓ c g₃) :=
    sixteen_mul_card_le inf_le_right inf_le_right inf_le_right (hle _ _ h12) (hle _ _ h13)
      (hle _ _ h23) (h4 g₂) (h4 g₃)
  have hP2 : 16 * Nat.card ↥(G₁ ⊓ G₂ ⊓ c g₂) ≤
      Nat.card ↥(G₁ ⊓ G₂ ⊓ c 1 ⊔ G₁ ⊓ G₂ ⊓ c g₂ ⊔ G₁ ⊓ G₂ ⊓ c g₃) := by
    have := sixteen_mul_card_le (X₁ := G₁ ⊓ G₂ ⊓ c g₂) (X₂ := G₁ ⊓ G₂ ⊓ c 1)
      (X₃ := G₁ ⊓ G₂ ⊓ c g₃) inf_le_right inf_le_right inf_le_right (hle _ _ (Ne.symm h12))
      (hle _ _ h23) (hle _ _ h13) (h4 1) (h4 g₃)
    rwa [sup_comm (G₁ ⊓ G₂ ⊓ c g₂) (G₁ ⊓ G₂ ⊓ c 1)] at this
  have hP3 : 16 * Nat.card ↥(G₁ ⊓ G₂ ⊓ c g₃) ≤
      Nat.card ↥(G₁ ⊓ G₂ ⊓ c 1 ⊔ G₁ ⊓ G₂ ⊓ c g₂ ⊔ G₁ ⊓ G₂ ⊓ c g₃) := by
    have := sixteen_mul_card_le (X₁ := G₁ ⊓ G₂ ⊓ c g₃) (X₂ := G₁ ⊓ G₂ ⊓ c 1)
      (X₃ := G₁ ⊓ G₂ ⊓ c g₂) inf_le_right inf_le_right inf_le_right (hle _ _ (Ne.symm h13))
      (hle _ _ (Ne.symm h23)) (hle _ _ h12) (h4 1) (h4 g₂)
    have e : G₁ ⊓ G₂ ⊓ c g₃ ⊔ G₁ ⊓ G₂ ⊓ c 1 ⊔ G₁ ⊓ G₂ ⊓ c g₂ =
        G₁ ⊓ G₂ ⊓ c 1 ⊔ G₁ ⊓ G₂ ⊓ c g₂ ⊔ G₁ ⊓ G₂ ⊓ c g₃ := by
      rw [sup_comm (G₁ ⊓ G₂ ⊓ c g₃) (G₁ ⊓ G₂ ⊓ c 1), sup_assoc,
        sup_comm (G₁ ⊓ G₂ ⊓ c g₃) (G₁ ⊓ G₂ ⊓ c g₂), ← sup_assoc]
    rwa [e] at this
  have hTN₀ : ¬ G₁ ⊓ G₂ ≤ (Subgroup.normalizer (K : Set D)).normalCore := by
    intro hle'
    have htop := eq_top_of_normal_of_inf_le hG hle'
    have hNtop : Subgroup.normalizer (K : Set D) = ⊤ :=
      top_le_iff.mp (htop ▸ (Subgroup.normalizer (K : Set D)).normalCore_le)
    apply hidx
    rw [hNtop, Subgroup.index_top]
    norm_num
  have hsq : ∀ g, Nat.card ↥(G₁ ⊓ G₂ ⊓ c g) ≤ 4 → ∀ x ∈ G₁ ⊓ G₂ ⊓ c g, x ^ 2 = 1 := by
    intro g hg x hx
    have h4' : Nat.card ↥(G₁ ⊓ G₂ ⊓ c g) = 4 := le_antisymm hg (hS4 g)
    exact sq_eq_one_of_card_eq_four h4'
      (not_isCyclic_of_isSylowIn (hc g).1 (hS g) (by omega)) hx
  obtain ⟨h128, hZ⟩ := card_inf_bound hlist h
  have hS41 := hS4 1
  refine false_of_three_commuting (T := G₁ ⊓ G₂) (N₀ := (Subgroup.normalizer (K : Set D)).normalCore)
    (S₁ := G₁ ⊓ G₂ ⊓ c 1) (S₂ := G₁ ⊓ G₂ ⊓ c g₂) (S₃ := G₁ ⊓ G₂ ⊓ c g₃)
    (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
    (sup_le (sup_le (inf_le_right.trans (map_conj_le_normalCore hK 1))
      (inf_le_right.trans (map_conj_le_normalCore hK g₂)))
      (inf_le_right.trans (map_conj_le_normalCore hK g₃))) hTN₀ (by omega) (fun h64 => ?_)
    (inf_le_right.trans ((hle _ _ h12).trans (Subgroup.centralizer_le inf_le_right)))
    (inf_le_right.trans ((hle _ _ h13).trans (Subgroup.centralizer_le inf_le_right)))
    (inf_le_right.trans ((hle _ _ h23).trans (Subgroup.centralizer_le inf_le_right))) h128 hZ
  exact ⟨hsq 1 (by omega), hsq g₂ (by omega), hsq g₃ (by omega)⟩

theorem eq_of_le_sup_of_isComponent {K K' Q : Subgroup D} [Q.Normal] (hQ : Group.IsSolvable ↥Q)
    (hK : CFSG.IsComponent K) (hK' : CFSG.IsComponent K') (hle : K' ≤ K ⊔ Q) : K' = K := by
  by_contra hne
  have hc : ⁅K, K'⁆ = ⊥ := (CFSG.LocalCores.distinct_components_commute hK hK').resolve_left
    (Ne.symm hne)
  have hKc : K ≤ Subgroup.centralizer (K' : Set D) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hQc : Q ≤ Subgroup.centralizer (K' : Set D) := by
    have h1 := (CFSG.LocalCores.component_solvable_centralizer hQ
      (inferInstance : Q.Normal).isSubnormal).1 K' hK'
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
  have hab : K' ≤ Subgroup.centralizer (K' : Set D) := hle.trans (sup_le hKc hQc)
  obtain ⟨-, -, a, b, hab'⟩ := hK'.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab'
  have : a * b = b * a :=
    Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hab a.2) b b.2).symm)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]

theorem normalizer_eq_comap_mk {K : Subgroup D} (hK : CFSG.IsComponent K) :
    Subgroup.normalizer (K : Set D) =
      (Subgroup.normalizer ((K.map (QuotientGroup.mk' (Open.pCore 2 D)) :
        Subgroup (D ⧸ Open.pCore 2 D)) : Set (D ⧸ Open.pCore 2 D))).comap
        (QuotientGroup.mk' (Open.pCore 2 D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : (Open.pCore 2 D).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have : Group.IsNilpotent ↥(Open.pCore 2 D) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup 2).isNilpotent
  have hQs : Group.IsSolvable ↥(Open.pCore 2 D) := inferInstance
  ext x
  rw [Subgroup.mem_comap, F6.mem_normalizer_iff_map_conj, F6.mem_normalizer_iff_map_conj]
  have hmap : (K.map (QuotientGroup.mk' (Open.pCore 2 D))).map
      (MulAut.conj (QuotientGroup.mk' (Open.pCore 2 D) x)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (QuotientGroup.mk' (Open.pCore 2 D)) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap]
  constructor
  · intro h
    rw [h]
  · intro h
    have hK' : CFSG.IsComponent (K.map (MulAut.conj x).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv _ hK
    refine eq_of_le_sup_of_isComponent hQs hK hK' ?_
    calc K.map (MulAut.conj x).toMonoidHom
        ≤ ((K.map (MulAut.conj x).toMonoidHom).map (QuotientGroup.mk' (Open.pCore 2 D))).comap
            (QuotientGroup.mk' (Open.pCore 2 D)) := Subgroup.le_comap_map _ _
      _ = (K.map (QuotientGroup.mk' (Open.pCore 2 D))).comap
            (QuotientGroup.mk' (Open.pCore 2 D)) := by rw [h]
      _ = K ⊔ Open.pCore 2 D := by rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem index_normalizer_le_two (hlist : GoldschmidtS3ListCat.{u}) {D : Type u} [Group D]
    [Finite D] {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂) {K : Subgroup D}
    (hK : CFSG.IsComponent K) : (Subgroup.normalizer (K : Set D)).index ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hπ : Function.Surjective (QuotientGroup.mk' (Open.pCore 2 D)) :=
    QuotientGroup.mk'_surjective _
  have hKQ : ¬ K ≤ (QuotientGroup.mk' (Open.pCore 2 D)).ker := by
    rw [QuotientGroup.ker_mk']
    intro hle
    have : Group.IsNilpotent ↥K :=
      ((CFSG.LieType.BorelTits.pCore_isPGroup 2).to_le hle).isNilpotent
    have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
    have : Group.IsPerfect ↥K := hK.1.1
    exact Group.IsPerfect.not_isSolvable ↥K inferInstance
  have hKb : CFSG.IsComponent (K.map (QuotientGroup.mk' (Open.pCore 2 D))) :=
    ⟨CFSG.LocalCores.isQuasisimple_map hK.1 _ hKQ, hK.2.map hπ⟩
  have hb := index_normalizer_le_two_of_amalgam hlist h.quotient_pCore hKb
  rw [normalizer_eq_comap_mk hK, Subgroup.index_comap_of_surjective _ hπ]
  exact hb

theorem f6_10_of_list (hlist : GoldschmidtS3ListCat.{u}) {D : Type u} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂) {K : Subgroup D}
    (hK : CFSG.IsComponent K) :
    K.Normal ∧ ((twoResidual G₁ ≤ K ∧ K ⊔ G₂ = ⊤) ∨ (twoResidual G₂ ≤ K ∧ K ⊔ G₁ = ⊤)) ∧
      ¬ K ≤ CFSG.pPrimeCore 3 D :=
  F6.f6_10 h hK (index_normalizer_le_two hlist h hK)

end CFSG.Quasithin.RonanF610
