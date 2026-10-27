module

public import CFSG.Quasithin.H13.NQS13410W
public import CFSG.Quasithin.H13.NQS13410I

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem pCoreOf_sup_R_le_R (S : A6.Setting134 G T L V) {K : Subgroup G}
    (hTK : T ≤ normalizer (K : Set G)) (hTsyl : IsSylowTwoOf T (K ⊔ T))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G)) :
    pCoreOf 2 (K ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hR
  have hRT : R ≤ T := s134_R_le_T S
  have hRK : R ≤ normalizer (K : Set G) := hRT.trans hTK
  have hL1TR : L₁ ⊔ T ≤ normalizer (R : Set G) := LieType.BorelTits.le_normalizer_pCoreOf 2 _
  set Y := pCoreOf 2 (K ⊔ R) with hY
  have hTKR : T ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) :=
    le_normalizer_sup_of hRK hTK (le_sup_right.trans hL1TR)
  have hL1KR : L₁ ≤ normalizer ((K ⊔ R : Subgroup G) : Set G) :=
    le_normalizer_sup_of hRK hL1K (le_sup_left.trans hL1TR)
  have hNY : normalizer ((K ⊔ R : Subgroup G) : Set G) ≤ normalizer (Y : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
  have hY2 : IsPGroup 2 ↥Y := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hYT : Y ≤ T := by
    have h1 : Y ≤ pCoreOf 2 (K ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_sup_left hRT K))
        ((sup_le (le_sup_left.trans le_normalizer) hTKR).trans hNY) hY2
    exact h1.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl)
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hYT.trans le_sup_right)
    ((sup_le hL1KR hTKR).trans hNY) hY2

theorem le_R_of_le (S : A6.Setting134 G T L V) {K U : Subgroup G}
    (hTK : T ≤ normalizer (K : Set G)) (hTsyl : IsSylowTwoOf T (K ⊔ T))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G)) (hUK : U ≤ K) (hU2 : IsPGroup 2 ↥U)
    (hKU : K ≤ normalizer (U : Set G)) (hTU : T ≤ normalizer (U : Set G)) :
    U ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T := s134_R_le_T S
  have h1 : U ≤ pCoreOf 2 (K ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hUK.trans le_sup_left)
      (sup_le hKU (hRT.trans hTU)) hU2
  exact h1.trans (pCoreOf_sup_R_le_R S hTK hTsyl hL1K)

theorem not_a5_of_hat (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hK5 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    [IsMulCommutative ↥W] (hW5 : AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5)
    (hKW : K ≤ normalizer (W : Set G)) (hTW : T ≤ normalizer (W : Set G)) (hWK : W ≤ K)
    (hWR : W ≤ reducedAggregate (K ⊔ T)) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hRdef
  obtain ⟨-, ⟨hTK, -, -, huniqK⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hZK := center_eq_bot_of_simple_types (Or.inl hK5)
  have hred := twoReduced_R2 (K ⊔ T)
  have hWe : IsElemAbelian 2 W := ⟨‹_›, fun w hw => hred.2.2.1.2 w (hWR hw)⟩
  have hW2 : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by simpa using hWe.2 w w.2)⟩
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  obtain ⟨R5⟩ := A5.exists_rawData5_of_nat hKW hW5
  have hW1 : W ≠ ⊥ := by
    intro h
    have h16 := Nat.card_congr R5.ψ.toEquiv
    rw [A5.card_W5, h, Subgroup.card_bot] at h16
    omega
  have hNL : normalizer (W : Set G) ≤ normalizer (K : Set G) := by
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨W, hW1, hW2, rfl⟩ : IsTwoLocal (normalizer (W : Set G)))
    have := huniqK M' hM' ((sup_le hKW hTW).trans hle)
    exact this ▸ hle
  obtain ⟨F⟩ := A5.exists_frame R5 hNL S.h13.sylow.1 hTW hsyl
  obtain ⟨g, hgK, hg⟩ := (F.image_L A5Model.c3p).2 A5.c3p_sign
  obtain ⟨⟨y, hyNW⟩, ⟨m, hm, hym⟩, hρy, j, hyj⟩ :=
    exists_odd_part F.ρ g (by rw [hg]; exact A5.c3p_cube)
  rw [hg] at hρy
  have hym' : y ^ m = 1 := hym
  have hyK : y ∈ K := by
    have hyj' : y = (g : G) ^ j := hyj
    rw [hyj']
    exact pow_mem hgK j
  have hyfix : ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y := by
    intro w hwW hwT
    have hfix : ∀ σ : Perm (Fin 5), A5.InK4 σ →
        A5Model.pact σ (F.ψ ⟨w, hwW⟩) = F.ψ ⟨w, hwW⟩ := by
      intro σ hσ
      obtain ⟨t, htT, rfl⟩ := F.K4_T σ hσ
      rw [← F.equiv t ⟨w, hwW⟩]
      congr 1
      apply Subtype.ext
      rw [A5.conjAct_val]
      have := mem_centralizer_iff.mp hwT (t : G) htT
      calc (t : G) * w * (t : G)⁻¹ = w * t * (t : G)⁻¹ := by rw [this]
        _ = w := by group
    have hy : A5Model.pact (F.ρ ⟨y, hyNW⟩) (F.ψ ⟨w, hwW⟩) = F.ψ ⟨w, hwW⟩ := by
      rw [hρy]
      rcases A5.fixed_K4 _ hfix with h1 | h4
      · rw [h1, map_one]
      · rw [h4]
        exact A5Model.pact_W4 A5.c3p_four
    rw [← F.equiv ⟨y, hyNW⟩ ⟨w, hwW⟩] at hy
    have h2 := congrArg Subtype.val (F.ψ.injective hy)
    rw [A5.conjAct_val] at h2
    have h2' : y * w * y⁻¹ = w := h2
    calc y * w = y * w * y⁻¹ * y := by group
      _ = w * y := by rw [h2']
  have hyZ := mem_centralizer_Z_of hTW hZW hyK hyfix
  have hyW : y ∉ centralizer (W : Set G) := fun h => by
    have h1 := A5.Frame.rho_eq_one_of_mem F ⟨y, hyNW⟩ h
    rw [hρy] at h1
    exact absurd h1 (by decide)
  have hy3 : y ^ 3 = 1 := by
    have h3 : F.ρ (⟨y, hyNW⟩ ^ 3) = 1 := by rw [map_pow, hρy, A5.c3p_cube]
    have h3C : y ^ 3 ∈ centralizer (W : Set G) := by
      simpa using A5.Frame.mem_centralizer_of_rho F (⟨y, hyNW⟩ ^ 3) h3
    have h1 : y ^ 3 ∈ A6.o2Z K := by rw [ho2Z]; exact mem_inf.2 ⟨pow_mem hyK 3, h3C⟩
    obtain ⟨s, hs⟩ :=
      LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, o2Z_le_pCoreOf_of_center hZK h1⟩
    have hs' : (y ^ 3) ^ 2 ^ s = 1 := by
      have := congrArg Subtype.val hs
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
      exact this
    have hm' : (y ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hym', one_pow]
    exact mem_bot.1 (mem_of_pow_odd_mem hs' hm (by rw [hm']; exact one_mem _))
  have hy1 : y ≠ 1 := fun h => hyW (h ▸ one_mem _)
  have hyL1 : y ∈ L₁ := mem_L1_of_orderOf_three h1332 h1228 S hyZ (orderOf_eq_prime hy3 hy1)
  have hRT : R ≤ T := s134_R_le_T S
  have hRN : R ≤ normalizer (W : Set G) := hRT.trans hTW
  have hWR' : W ≤ R := le_R_of_le S hTK hTsyl hL1K hWK hW2 hKW hTW
  have hyR : y ∈ normalizer (R : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T) (mem_sup_left hyL1)
  have hRK4 : ∀ r : ↥(normalizer (W : Set G)), (r : G) ∈ R → A5.InK4 (F.ρ r) := by
    intro r hr
    have hyr : y * r * y⁻¹ ∈ R := (mem_normalizer_iff.mp hyR r).mp hr
    have h2 := F.T_D (⟨y, hyNW⟩ * r * ⟨y, hyNW⟩⁻¹) (hRT hyr)
    rw [map_mul, map_mul, map_inv, hρy] at h2
    exact inK4_of_conj_c3p _ (F.T_D r (hRT hr)) h2
  have hJ : thompsonJ R ≤ centralizer (W : Set G) :=
    iSup₂_le fun A hA => a5Frame_le_centralizer_of_isMaxElemAbelian F hWe hWR' hRN hRK4 hA
  have hCK2 : IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) := by
    rw [← ho2Z]
    exact (LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le (o2Z_le_pCoreOf_of_center hZK)
  exact false_of_thompsonJ_le_centralizer S hhat hKM hTK hTsyl hL1K hKW hTW hCK2 hJ

theorem not_case1ii_of_hat (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V) (hhat : A6.IsHatA6 L) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKM : ¬ K ≤ normalizer (L : Set G))
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    [IsMulCommutative ↥W] (hnatW : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1)
    (hKW : K ≤ normalizer (W : Set G)) (hTW : T ≤ normalizer (W : Set G))
    (hWU : W ≤ ⁅reducedAggregate (K ⊔ T), K⁆) (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    [IsMulCommutative ↥(reducedAggregate (K ⊔ T))]
    {J : Subgroup (MulAut ↥(reducedAggregate (K ⊔ T)))}
    (hii : B51Case1ii J (autOn K (reducedAggregate (K ⊔ T))))
    (hZ : quasithinOmegaOneCenter T ≤ ⁅reducedAggregate (K ⊔ T), K⁆ ⊔ U3.cZ T K) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R2 := reducedAggregate (K ⊔ T) with hR2def
  set U := ⁅R2, K⁆ with hUdef
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set R := pCoreOf 2 (L₁ ⊔ T) with hRdef
  set Q := pCoreOf 2 (K ⊔ T) with hQdef
  obtain ⟨-, ⟨hTK, -, -, -⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    center_eq_bot_of_simple_types (Or.inr (Or.inl hK3))
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hred := twoReduced_R2 (K ⊔ T)
  have hR2e : IsElemAbelian 2 R2 := hred.2.2.1
  have hcomm : ∀ a ∈ R2, ∀ b ∈ R2, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hR2e.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hKR2 : K ≤ normalizer (R2 : Set G) := le_sup_left.trans hred.2.1
  have hR2Q : R2 ≤ Q := R2_le_pCoreOf (K ⊔ T)
  have hQC : Q ≤ centralizer (R2 : Set G) := pCoreOf_le_centralizer_R2 (K ⊔ T)
  have hQT : Q ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTsyl
  have h168 : Nat.card ↥(autOn K R2) ≤ 168 := by
    have h1 := U3.card_autOn_le_card_quot hKR2
      ((A6.pCoreOf_le_pCoreOf_sup hTK).trans hQC)
    rwa [card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 hK3)] at h1
  obtain ⟨I₀, I₁, hI₀R, hI₁R, hKI₀, hKI₁, hinf, hsup, ⟨hc₀, hnat₀⟩, φ, hφ⟩ :=
    exists_two_copies hKR2 hii h168
  have hc₁ : IsMulCommutative ↥I₁ := isMulCommutative_of_le' hI₁R
  have hsup' : I₀ ⊔ I₁ = U := hsup
  have hUR2 : U ≤ R2 := by rw [← hsup']; exact sup_le hI₀R hI₁R
  have hI₀U : I₀ ≤ U := by rw [← hsup']; exact le_sup_left
  have hI₁U : I₁ ≤ U := by rw [← hsup']; exact le_sup_right
  have hUe : IsElemAbelian 2 U := ⟨isMulCommutative_of_le' hUR2, fun u hu => hR2e.2 u (hUR2 hu)⟩
  have hU2 : IsPGroup 2 ↥U := fun u => ⟨1, Subtype.ext (by simpa using hUe.2 u u.2)⟩
  have hnorm : ∀ {A B : Subgroup G}, A ≤ R2 → B ≤ R2 → B ≤ normalizer (A : Set G) :=
    fun {A B} hA hB => A5.le_normalizer_of_forall_conj_mem fun b hb a ha => by
      rw [hcomm b (hB hb) a (hA ha), mul_inv_cancel_right]
      exact ha
  have hI₁N : I₁ ≤ normalizer (I₀ : Set G) := hnorm hI₀R hI₁R
  have h8₀ : Nat.card ↥I₀ = 8 := card_eq_eight_of_l32 hnat₀
  have h8₁ : Nat.card ↥I₁ = 8 := by
    have := Nat.card_congr φ.toEquiv
    rw [← this, h8₀]
  have htopW := autOn_eq_top_of_l32 hnatW
  have hCW2 : IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) := by
    rw [← ho2Z]
    exact (LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le (o2Z_le_pCoreOf_of_center hZK)
  have hTact : ∀ t ∈ T, ∃ k ∈ K, ∀ u ∈ R2, t * u * t⁻¹ = k * u * k⁻¹ := fun t ht =>
    exists_conj_R2 hTsyl hTK hKW hTW htopW hCW2 ht
  have hTI : ∀ {I : Subgroup G}, I ≤ R2 → K ≤ normalizer (I : Set G) →
      T ≤ normalizer (I : Set G) := fun {I} hIR hKI =>
    A5.le_normalizer_of_forall_conj_mem fun t ht x hx => by
      obtain ⟨k, hk, hkt⟩ := hTact t ht
      rw [hkt x (hIR hx)]
      exact (mem_normalizer_iff.mp (hKI hk) x).mp hx
  have hTI₀ := hTI hI₀R hKI₀
  have hTI₁ := hTI hI₁R hKI₁
  have hKU : K ≤ normalizer (U : Set G) := A5.le_normalizer_of_forall_conj_mem fun k hk x hx => by
    rw [← hsup'] at hx ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hI₁N hx
    have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hKI₀ hk) a).mp ha))
      (mem_sup_right ((mem_normalizer_iff.mp (hKI₁ hk) b).mp hb))
  have hTU : T ≤ normalizer (U : Set G) := A5.le_normalizer_of_forall_conj_mem fun t ht x hx => by
    rw [← hsup'] at hx ⊢
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hI₁N hx
    have e : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.mp (hTI₀ ht) a).mp ha))
      (mem_sup_right ((mem_normalizer_iff.mp (hTI₁ ht) b).mp hb))
  have hφT : ∀ t ∈ T, ∀ (u : ↥I₀) (hu : t * (u : G) * t⁻¹ ∈ I₀),
      ((φ ⟨t * u * t⁻¹, hu⟩ : ↥I₁) : G) = t * (φ u : G) * t⁻¹ := by
    intro t ht u hu
    obtain ⟨k, hk, hkt⟩ := hTact t ht
    have hu' : k * (u : G) * k⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hk) u).mp u.2
    have e1 : (⟨t * u * t⁻¹, hu⟩ : ↥I₀) = ⟨k * u * k⁻¹, hu'⟩ := Subtype.ext (hkt u (hI₀R u.2))
    rw [e1, hφ k hk u hu', hkt _ (hI₁R (φ u).2)]
  have hCI₀₁ : ∀ k ∈ K, k ∈ centralizer (I₀ : Set G) → k ∈ centralizer (I₁ : Set G) := by
    intro k hk hkC
    rw [mem_centralizer_iff]
    intro v hv
    set u : ↥I₀ := φ.symm ⟨v, hv⟩ with hu
    have hφu : φ u = ⟨v, hv⟩ := by rw [hu, MulEquiv.apply_symm_apply]
    have hku : k * (u : G) * k⁻¹ = u := by
      rw [← mem_centralizer_iff.mp hkC u u.2, mul_inv_cancel_right]
    have hu' : k * (u : G) * k⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hk) u).mp u.2
    have h1 := hφ k hk u hu'
    have h2 : (⟨k * (u : G) * k⁻¹, hu'⟩ : ↥I₀) = u := Subtype.ext hku
    rw [h2, hφu] at h1
    have h3 : k * v * k⁻¹ = v := h1.symm
    calc v * k = k * v * k⁻¹ * k := by rw [h3]
      _ = k * v := by group
  have hCKU : ∀ k ∈ K, k ∈ centralizer (I₀ : Set G) → k ∈ centralizer (U : Set G) := by
    intro k hk hkC
    have hk₁ := hCI₀₁ k hk hkC
    rw [mem_centralizer_iff]
    intro x hx
    rw [← hsup'] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hI₁N hx
    calc a * b * k = a * (k * b) := by rw [mul_assoc, mem_centralizer_iff.mp hk₁ b hb]
      _ = k * (a * b) := by rw [← mul_assoc, mem_centralizer_iff.mp hkC a ha, mul_assoc]
  have hCK₀ : IsPGroup 2 ↥(K ⊓ centralizer (I₀ : Set G)) := hCW2.to_le fun k hk =>
    mem_inf.2 ⟨(mem_inf.1 hk).1, centralizer_le (SetLike.coe_subset_coe.mpr hWU)
      (hCKU k (mem_inf.1 hk).1 (mem_inf.1 hk).2)⟩
  have hCI₁₀ : ∀ k ∈ K, k ∈ centralizer (I₁ : Set G) → k ∈ centralizer (I₀ : Set G) := by
    intro k hk hkC
    rw [mem_centralizer_iff]
    intro u hu
    have hu' : k * u * k⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hk) u).mp hu
    have h1 := hφ k hk ⟨u, hu⟩ hu'
    have h2 : k * (φ ⟨u, hu⟩ : G) * k⁻¹ = φ ⟨u, hu⟩ := by
      rw [← mem_centralizer_iff.mp hkC _ (φ ⟨u, hu⟩).2, mul_inv_cancel_right]
    rw [h2] at h1
    have h3 := φ.injective (Subtype.ext h1)
    have h4 : k * u * k⁻¹ = u := congrArg Subtype.val h3
    calc u * k = k * u * k⁻¹ * k := by rw [h4]
      _ = k * u := by group
  have hCK₁ : IsPGroup 2 ↥(K ⊓ centralizer (I₁ : Set G)) := hCK₀.to_le fun k hk =>
    mem_inf.2 ⟨(mem_inf.1 hk).1, hCI₁₀ k (mem_inf.1 hk).1 (mem_inf.1 hk).2⟩
  have hCKU2 : IsPGroup 2 ↥(K ⊓ centralizer (U : Set G)) := hCK₀.to_le fun k hk =>
    mem_inf.2 ⟨(mem_inf.1 hk).1, centralizer_le (SetLike.coe_subset_coe.mpr hI₀U)
      (mem_inf.1 hk).2⟩
  have hQ₀ : T ⊓ centralizer (I₀ : Set G) = Q :=
    U3.inf_centralizer_eq_pCoreOf_sup hTsyl hTK hKI₀ hTI₀
      (le_centralizer_iff.mp (hQC.trans (centralizer_le hI₀R))) hCK₀
  have hQ₁ : T ⊓ centralizer (I₁ : Set G) = Q :=
    U3.inf_centralizer_eq_pCoreOf_sup hTsyl hTK hKI₁ hTI₁
      (le_centralizer_iff.mp (hQC.trans (centralizer_le hI₁R))) hCK₁
  have hQU : Q ≤ centralizer (U : Set G) := hQC.trans (centralizer_le hUR2)
  have hI₀T : I₀ ≤ T := hI₀R.trans (hR2Q.trans hQT)
  have hI₀1 : I₀ ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at h8₀; omega
  obtain ⟨x₀', hx₀I, hx₀T, hx₀1'⟩ :=
    exists_mem_centralizer_ne_one hKf.1.1 hI₀T hTI₀ hI₀1
  set x₀ : ↥I₀ := ⟨x₀', hx₀I⟩ with hx₀def
  have hx₀1 : x₀ ≠ 1 := fun h => hx₀1' (congrArg Subtype.val h)
  obtain ⟨y, hyK, ⟨m, hm, hym⟩, hyI₀, hy3I₀, hyfix₀⟩ := exists_three_of_l32 hKI₀ hnat₀ hsyl
  have hy3 : y ^ 3 = 1 := by
    obtain ⟨s, hs⟩ := hCK₀ ⟨_, mem_inf.2 ⟨pow_mem hyK 3, hy3I₀⟩⟩
    have hs' : (y ^ 3) ^ 2 ^ s = 1 := by
      have h2 := congrArg Subtype.val hs
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    have hm' : (y ^ 3) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hym, one_pow]
    exact mem_bot.1 (mem_of_pow_odd_mem hs' hm (by rw [hm']; exact one_mem _))
  have hy1 : y ≠ 1 := fun h => hyI₀ (h ▸ one_mem _)
  have hyfix₁ : ∀ v ∈ I₁, v ∈ centralizer (T : Set G) → y * v = v * y := by
    intro v hv hvT
    set u : ↥I₀ := φ.symm ⟨v, hv⟩ with hu
    have hφu : φ u = ⟨v, hv⟩ := by rw [hu, MulEquiv.apply_symm_apply]
    have huT : (u : G) ∈ centralizer (T : Set G) := by
      rw [mem_centralizer_iff]
      intro t ht
      have htu : t * (u : G) * t⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hTI₀ ht) u).mp u.2
      have h1 := hφT t ht u htu
      rw [hφu] at h1
      have h2 : t * v * t⁻¹ = v := by rw [mem_centralizer_iff.mp hvT t ht, mul_inv_cancel_right]
      have h3 : φ ⟨t * (u : G) * t⁻¹, htu⟩ = φ u := by
        rw [hφu]
        apply Subtype.ext
        rw [h1]
        exact h2
      have h4 : t * (u : G) * t⁻¹ = u := congrArg Subtype.val (φ.injective h3)
      calc t * (u : G) = t * u * t⁻¹ * t := by group
        _ = u * t := by rw [h4]
    have h1 := hyfix₀ u u.2 huT
    have hyu : y * (u : G) * y⁻¹ ∈ I₀ := (mem_normalizer_iff.mp (hKI₀ hyK) u).mp u.2
    have h2 := hφ y hyK u hyu
    have h3 : (⟨y * (u : G) * y⁻¹, hyu⟩ : ↥I₀) = u :=
      Subtype.ext (show y * (u : G) * y⁻¹ = u by rw [h1, mul_inv_cancel_right])
    rw [h3, hφu] at h2
    have h2' : y * v * y⁻¹ = v := h2.symm
    calc y * v = y * v * y⁻¹ * y := by group
      _ = v * y := by rw [h2']
  have hyfixU : ∀ u ∈ U, u ∈ centralizer (T : Set G) → y * u = u * y := by
    intro x hx hxT
    rw [← hsup'] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hI₁N hx
    have hab : ∀ t ∈ T, t * a * t⁻¹ = a ∧ t * b * t⁻¹ = b := fun t ht =>
      conj_eq_of_mul hinf ha hb (hTI₀ ht) (hTI₁ ht) (by
        rw [mem_centralizer_iff.mp hxT t ht, mul_inv_cancel_right])
    have haT : a ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
      calc t * a = t * a * t⁻¹ * t := by group
        _ = a * t := by rw [(hab t ht).1]
    have hbT : b ∈ centralizer (T : Set G) := mem_centralizer_iff.2 fun t ht => by
      calc t * b = t * b * t⁻¹ * t := by group
        _ = b * t := by rw [(hab t ht).2]
    calc y * (a * b) = (y * a) * b := by group
      _ = a * (y * b) := by rw [hyfix₀ a ha haT, mul_assoc]
      _ = a * b * y := by rw [hyfix₁ b hb hbT, mul_assoc]
  have hyZ := mem_centralizer_Z_of hTU hZ hyK hyfixU
  have hyL1 : y ∈ L₁ := mem_L1_of_orderOf_three h1332 h1228 S hyZ (orderOf_eq_prime hy3 hy1)
  have hRT : R ≤ T := s134_R_le_T S
  have hR2' : IsPGroup 2 ↥R := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hUK : U ≤ K :=
    le_normalizer_iff_commutator_le_right.mp ((hR2Q.trans hQT).trans hTK)
  have hUR : U ≤ R := le_R_of_le S hTK hTsyl hL1K hUK hU2 hKU hTU
  have hyR : y ∈ normalizer (R : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (L₁ ⊔ T) (mem_sup_left hyL1)
  have hRN₀ : R ≤ normalizer (I₀ : Set G) := hRT.trans hTI₀
  obtain ⟨C⟩ := exists_l3Coords hnat₀
  set yN : ↥(normalizer (I₀ : Set G)) := ⟨y, hKI₀ hyK⟩ with hyN
  have hρy3 : C.ρ yN ^ 3 = 1 := by
    rw [← map_pow]
    have : yN ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, hyN, Subgroup.coe_one]
      exact hy3)
    rw [this, map_one]
  have hρy1 : C.ρ yN ≠ 1 := fun h => hyI₀ ((C.ker yN).1 h)
  have hρyp : L3.act (C.ρ yN) (C.c x₀) = C.c x₀ := by
    refine (C.fix_iff yN x₀).1 ?_
    show y * x₀' * y⁻¹ = x₀'
    rw [hyfix₀ x₀' hx₀I hx₀T, mul_inv_cancel_right]
  have hRfix : ∀ r ∈ R, r * (x₀ : G) * r⁻¹ = x₀ := fun r hr => by
    show r * x₀' * r⁻¹ = x₀'
    rw [mem_centralizer_iff.mp hx₀T r (hRT hr), mul_inv_cancel_right]
  have hRE : ∀ r : ↥(normalizer (I₀ : Set G)), (r : G) ∈ R → C.ρ r ∈ L3.AS {0, C.c x₀} :=
    fun r hr => C.rho_mem_AS hR2' hx₀1 hRfix yN hρy3 hρy1 hρyp hyR r hr
  have hp0 : C.c x₀ ≠ 0 := C.c_ne_zero hx₀1
  have hJ : thompsonJ R ≤ centralizer (U : Set G) := by
    refine iSup₂_le fun A hA => ?_
    by_contra hAC
    have hAR := hA.1
    have hA₀ : ¬ A ≤ centralizer (I₀ : Set G) := fun h => hAC fun a ha =>
      hQU (hQ₀ ▸ mem_inf.2 ⟨hRT (hAR ha), h ha⟩)
    have hA₁ : ¬ A ≤ centralizer (I₁ : Set G) := fun h => hAC fun a ha =>
      hQU (hQ₁ ▸ mem_inf.2 ⟨hRT (hAR ha), h ha⟩)
    have hle := card_le_relIndex_mul_card hUe hUR hA
    have hAU : A ⊓ centralizer (U : Set G) = A ⊓ centralizer (I₀ : Set G) := by
      refine le_antisymm (inf_le_inf_left _ (centralizer_le hI₀U)) fun a ha => ?_
      refine mem_inf.2 ⟨(mem_inf.1 ha).1, hQU ?_⟩
      rw [← hQ₀]
      exact mem_inf.2 ⟨hRT (hAR (mem_inf.1 ha).1), (mem_inf.1 ha).2⟩
    have h1 := C.relIndex_mul_card_le (hAR.trans hRN₀) hp0 (fun a ha => hRE a (hAR ha)) hA₀
    have h2 : Nat.card ↥(U ⊓ centralizer (A : Set G)) ≤
        Nat.card ↥(I₀ ⊓ centralizer (A : Set G)) * Nat.card ↥(I₁ ⊓ centralizer (A : Set G)) := by
      have := card_inf_centralizer_le hinf hI₁N (hAR.trans hRN₀) (hAR.trans (hRT.trans hTI₁))
      rwa [hsup'] at this
    have h3 : Nat.card ↥(I₁ ⊓ centralizer (A : Set G)) ≤ 4 := by
      refine card_le_four_of_lt h8₁ inf_le_left fun h => hA₁ ?_
      intro a ha
      rw [mem_centralizer_iff]
      intro v hv
      have hv' : v ∈ I₁ ⊓ centralizer (A : Set G) := by rw [h]; exact hv
      exact (mem_centralizer_iff.mp (mem_inf.1 hv').2 a ha).symm
    have hU64 : 64 ≤ Nat.card ↥U := by
      have := card_mul_le_card_sup hinf
      rw [h8₀, h8₁, hsup'] at this
      exact this
    rw [hAU] at hle
    have h4 : Nat.card ↥U ≤ 8 * 4 := by
      calc Nat.card ↥U ≤ (A ⊓ centralizer (I₀ : Set G)).relIndex A *
            Nat.card ↥(U ⊓ centralizer (A : Set G)) := hle
        _ ≤ (A ⊓ centralizer (I₀ : Set G)).relIndex A *
            (Nat.card ↥(I₀ ⊓ centralizer (A : Set G)) *
              Nat.card ↥(I₁ ⊓ centralizer (A : Set G))) := Nat.mul_le_mul_left _ h2
        _ = (A ⊓ centralizer (I₀ : Set G)).relIndex A *
            Nat.card ↥(I₀ ⊓ centralizer (A : Set G)) *
              Nat.card ↥(I₁ ⊓ centralizer (A : Set G)) := by ring
        _ ≤ 8 * 4 := Nat.mul_le_mul h1 h3
    omega
  exact false_of_thompsonJ_le_centralizer S hhat hKM hTK hTsyl hL1K hKU hTU hCKU2 hJ

end CFSG.Quasithin.H13.NQS134
