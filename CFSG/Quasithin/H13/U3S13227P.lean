module

public import CFSG.Quasithin.H13.U3S13227H
public import CFSG.Quasithin.H13.A6S13227

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

theorem inA4_cube_mem_C3 : ∀ σ : Perm (Fin 6), InA4 σ → σ ^ 3 = 1 → σ ∈ S14.C3 := by
  decide +kernel

@[expose] def span8 (a b : P6) : Finset P6 :=
  {1, G6.allOnes 6, a, a * G6.allOnes 6, b, b * G6.allOnes 6, a * b, a * b * G6.allOnes 6}

@[expose] def Indep8 (a b : P6) : Prop :=
  a ≠ 1 ∧ a ≠ G6.allOnes 6 ∧ b ≠ 1 ∧ b ≠ G6.allOnes 6 ∧ b ≠ a ∧ b ≠ a * G6.allOnes 6

instance (a b : P6) : Decidable (Indep8 a b) := by unfold Indep8; infer_instance

@[expose] def Line8 (a b : P6) : Prop :=
  ∑ i, Multiplicative.toAdd a i = 0 → ∑ i, Multiplicative.toAdd b i = 0 → Indep8 a b →
    (span8 a b).card = 8 ∧
      ¬ (G6.permAct 6 c012 a ∈ span8 a b ∧ G6.permAct 6 c012 b ∈ span8 a b ∧
        G6.permAct 6 c123 a ∈ span8 a b ∧ G6.permAct 6 c123 b ∈ span8 a b)

instance (a b : P6) : Decidable (Line8 a b) := by unfold Line8; infer_instance

theorem line8_all : ∀ a b : P6, Line8 a b := by decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_exists_oTwoRes_rho (S : A6.Setting134 G T L V) {X : Subgroup G}
    {c : ↥(normalizer (V : Set G))} (hc : (c : G) ∈ X) {σ : Perm (Fin 6)}
    (hρ : S.frame.ρ c = σ) (h3 : σ ^ 3 = 1) :
    ∃ y : ↥(normalizer (V : Set G)), (y : G) ∈ oTwoRes X ∧ S.frame.ρ y = σ := by
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨c ^ 4 ^ a, subset_closure ⟨by simpa using X.pow_mem hc (4 ^ a), m, hm, ?_⟩,
    by rw [map_pow, hρ, pow_four_pow_of_cube h3]⟩
  have h1 : (c ^ (4 ^ a)) ^ m = (c ^ (2 ^ a * m)) ^ (2 ^ a) := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    ring
  have h2 : c ^ (2 ^ a * m) = 1 := by rw [← hnm, pow_orderOf_eq_one]
  have h3' : (c ^ (4 ^ a)) ^ m = 1 := by rw [h1, h2, one_pow]
  simpa using congrArg Subtype.val h3'

theorem s134_L1_three (S : A6.Setting134 G T L V) :
    ∀ τ ∈ S14.C3, ∃ x : ↥(normalizer (V : Set G)), (x : G) ∈ L₁Of L (fsuV1 T V) ∧
      S.frame.ρ x = τ := by
  intro τ hτ
  obtain ⟨h4, h5, hs, h3⟩ := S14.c3_facts τ hτ
  obtain ⟨y, hyL, hy, hρ⟩ :=
    s134_exists_mem_L1 S (Perm.mem_alternatingGroup.2 hs) h3 ⟨h4, h5, hs⟩
  exact ⟨⟨y, hy⟩, hyL, hρ⟩

theorem s134Plus_L1 (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) :
    S134Plus S (L₁Of L (fsuV1 T V)) where
  eq := S14.oTwoRes_idem _
  le_L1 := le_rfl
  T_le := s134_T_le_normalizer_L1 S
  three := s134_L1_three S
  cent := fun _ hx => o2Z_le_pCoreOf_of_a6 he (s134_centralizer_le_o2Z S
    ⟨((oTwoRes_le _).trans inf_le_left) hx.1, hx.2⟩)

theorem s134_commutator_L1_TL_le (S : A6.Setting134 G T L V) :
    ⁅L₁Of L (fsuV1 T V), T ⊓ L⁆ ≤ L₁Of L (fsuV1 T V) := by
  rw [commutator_le]
  intro h hh k hk
  have e : ⁅h, k⁆ = h * (k * h⁻¹ * k⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem hh ((mem_normalizer_iff.mp (s134_T_le_normalizer_L1 S hk.1) h⁻¹).mp
    (inv_mem hh))

theorem s134Plus_l1plus (S : A6.Setting134 G T L V) (hhat : IsHatA6 L) :
    S134Plus S (l1plus T L V) := by
  have hle : l1plus T L V ≤ L₁Of L (fsuV1 T V) :=
    (oTwoRes_le _).trans (s134_commutator_L1_TL_le S)
  refine ⟨S14.oTwoRes_idem _, hle, ?_, ?_, ?_⟩
  · exact A5.le_normalizer_oTwoRes_of_le_normalizer (A5.le_normalizer_commutator
      (s134_T_le_normalizer_L1 S) (F7.le_normalizer_inf le_normalizer S.T_le_NL))
  · obtain ⟨hD, hs, -⟩ := S14.t0_facts
    obtain ⟨t, htTL, hρt⟩ := s134_exists_TL S hD (Perm.mem_alternatingGroup.2 hs)
    obtain ⟨ha, hb, hab⟩ := S14.ab_facts
    have hlift : ∀ τ₀ : Perm (Fin 6), τ₀ ∈ S14.C3 → ∀ σ : Perm (Fin 6), σ ^ 3 = 1 →
        τ₀ * (swap 0 1 * swap 4 5) * τ₀⁻¹ * (swap 0 1 * swap 4 5)⁻¹ = σ →
        ∃ y : ↥(normalizer (V : Set G)), (y : G) ∈ l1plus T L V ∧ S.frame.ρ y = σ := by
      intro τ₀ hτ₀ σ hσ3 hσ
      obtain ⟨x, hxL, hρx⟩ := s134_L1_three S τ₀ hτ₀
      have hc : ((x * t * x⁻¹ * t⁻¹ : ↥(normalizer (V : Set G))) : G) ∈
          ⁅L₁Of L (fsuV1 T V), T ⊓ L⁆ := by
        have := commutator_mem_commutator hxL htTL
        rw [commutatorElement_def] at this
        exact this
      exact s134_exists_oTwoRes_rho S hc
        (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρx, hρt]; exact hσ) hσ3
    obtain ⟨ya, hya, hρa⟩ :=
      hlift (swap 0 1 * swap 1 2) (by decide) _ (S14.c3_facts _ (by decide)).2.2.2 ha
    obtain ⟨yb, hyb, hρb⟩ :=
      hlift (swap 0 1 * swap 1 3) (by decide) _ (S14.c3_facts _ (by decide)).2.2.2 hb
    intro τ hτ
    obtain ⟨x₁, hx₁, x₂, hx₂, m, n, hτe⟩ := hab τ hτ
    have hpick : ∀ x ∈ [(1 : Perm (Fin 6)), swap 0 2 * swap 2 1, swap 0 3 * swap 3 1],
        ∃ y : ↥(normalizer (V : Set G)), (y : G) ∈ l1plus T L V ∧ S.frame.ρ y = x := by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, one_mem _, map_one _⟩
      · exact ⟨ya, hya, hρa⟩
      · exact ⟨yb, hyb, hρb⟩
    obtain ⟨y₁, hy₁, hρ₁⟩ := hpick x₁ hx₁
    obtain ⟨y₂, hy₂, hρ₂⟩ := hpick x₂ hx₂
    refine ⟨y₁ ^ (m : ℕ) * y₂ ^ (n : ℕ), ?_, by rw [map_mul, map_pow, map_pow, hρ₁, hρ₂, hτe]⟩
    simpa using (l1plus T L V).mul_mem ((l1plus T L V).pow_mem hy₁ (m : ℕ))
      ((l1plus T L V).pow_mem hy₂ (n : ℕ))
  · intro x hx
    exact s134_hatL1Plus S hhat ⟨hx.1, s134_centralizer_le_o2Z S
      ⟨((hle.trans ((oTwoRes_le _).trans inf_le_left)) hx.1), hx.2⟩⟩

theorem s134_l0_le_L1 (S : A6.Setting134 G T L V) :
    l0 L ≤ L₁Of L (fsuV1 T V) := by
  show oTwoRes (o2Z L) ≤ oTwoRes (L ⊓ normalizer (fsuV1 T V : Set G))
  refine oTwoRes_mono fun y hy => ⟨o2Z_le_L hy, centralizer_le_normalizer _ ?_⟩
  exact centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left)
    (s134_o2Z_le_centralizer S hy)

namespace S134Plus

variable {S : A6.Setting134 G T L V} {Lp : Subgroup G} (P : S134Plus S Lp)
include P

theorem L1_le_l0_sup (hhat : IsHatA6 L) : L₁Of L (fsuV1 T V) ≤ l0 L ⊔ (Lp ⊔ T) := by
  change oTwoRes (L ⊓ normalizer (fsuV1 T V : Set G)) ≤ _
  rw [oTwoRes, closure_le]
  rintro y ⟨⟨hyL, hyN⟩, m, hm, hym⟩
  set yN : ↥(normalizer (V : Set G)) := ⟨y, S.frame.L_le hyL⟩ with hyNdef
  have hpres := s134_pres45 S yN hyN
  have hpow : S.frame.ρ yN ^ m = 1 := by
    rw [← map_pow]
    have : yN ^ m = 1 := Subtype.ext (by simpa using hym)
    rw [this, map_one]
  have hA4 := inA4_of_pres45 _ hpres (pow_45_of_odd' hm hpow)
  have h3 := cube_of_inA4 _ hA4 (pow_45_of_odd' hm hpow)
  obtain ⟨x, hxLp, hxρ⟩ := P.three _ (inA4_cube_mem_C3 _ hA4 h3)
  have hk : S.frame.ρ (x⁻¹ * yN) = 1 := by rw [map_mul, map_inv, hxρ, inv_mul_cancel]
  have hkC := (s134_rho_eq_one_iff S _).1 hk
  have hkL : ((x⁻¹ * yN : ↥(normalizer (V : Set G))) : G) ∈ L := by
    simpa [hyNdef] using L.mul_mem (L.inv_mem (P.le_L hxLp)) hyL
  have hkZ := o2Z_le_l0_sup hhat (s134_centralizer_le_o2Z S ⟨hkL, hkC⟩)
  have hOT : pCoreOf 2 L ≤ T :=
    (A6.pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  have hkX : ((x⁻¹ * yN : ↥(normalizer (V : Set G))) : G) ∈ l0 L ⊔ (Lp ⊔ T) :=
    sup_le_sup_left (hOT.trans le_sup_right) _ hkZ
  have e : y = (x : G) * ((x⁻¹ * yN : ↥(normalizer (V : Set G))) : G) := by
    simp [hyNdef]
  rw [e]
  exact mul_mem (mem_sup_right (mem_sup_left hxLp)) hkX

theorem hat_index (hhat : IsHatA6 L) :
    (Lp ⊔ T).relIndex (L₁Of L (fsuV1 T V) ⊔ T) = 3 := by
  have hle : Lp ⊔ T ≤ L₁Of L (fsuV1 T V) ⊔ T := sup_le_sup_right P.le_L1 T
  have heq : L₁Of L (fsuV1 T V) ⊔ T = l0 L ⊔ (Lp ⊔ T) := by
    apply le_antisymm
    · exact sup_le (P.L1_le_l0_sup hhat) (le_sup_right.trans le_sup_right)
    · exact sup_le ((s134_l0_le_L1 S).trans le_sup_left) hle
  have hN : Lp ⊔ T ≤ normalizer (l0 L : Set G) :=
    sup_le (P.le_L.trans L_le_normalizer_l0)
      (A5.le_normalizer_oTwoRes_of_le_normalizer (S.T_le_NL.trans normalizer_L_le_o2Z))
  rw [heq, relIndex_sup_of_normalizes hN]
  obtain ⟨c, hc, hc3, hcO, hdec⟩ := l0_decomp hhat
  have hOT : pCoreOf 2 L ≤ T :=
    (A6.pCoreOf_le_pCoreOf_sup S.T_le_NL).trans (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)
  have hO : pCoreOf 2 (l0 L) ≤ (Lp ⊔ T) ⊓ l0 L :=
    le_inf ((pCoreOf_l0_le.trans hOT).trans le_sup_right) (pCoreOf_le 2 _)
  refine relIndex_eq_three hc ?_ hc3 fun x hx => ?_
  · rintro ⟨hcP, -⟩
    have hcC : c ∈ centralizer (V : Set G) := s134_o2Z_le_centralizer S (oTwoRes_le _ hc)
    have hcT : c ∈ T := P.sup_inf_centralizer_le_T ⟨hcP, hcC⟩
    obtain ⟨k, hk⟩ := S.h13.sylow.1 ⟨c, hcT⟩
    have hc1 : c = 1 := cube_two_pow_eq_one (by simpa using congrArg Subtype.val hk) hc3
    exact hcO (hc1 ▸ one_mem _)
  · rcases hdec x hx with h | h | h
    · exact Or.inl (hO h)
    · exact Or.inr (Or.inl (hO h))
    · exact Or.inr (Or.inr (hO h))

theorem not_oTwoUpper_le_o2Z :
    ¬ oTwoUpper (Lp ⊔ T) ≤ o2Z L := by
  intro h
  have hLp : Lp ≤ o2Z L := by
    have h1 : oTwoUpper Lp ≤ oTwoUpper (Lp ⊔ T) := by
      rw [← oTwoRes_eq_oTwoUpper, ← oTwoRes_eq_oTwoUpper]
      exact oTwoRes_mono le_sup_left
    rw [← oTwoRes_eq_oTwoUpper, P.eq] at h1
    exact h1.trans h
  obtain ⟨x, hxLp, hxρ⟩ := P.three (swap 0 1 * swap 1 2) (by decide)
  have h1 := (s134_rho_eq_one_iff S x).2 (s134_o2Z_le_centralizer S (hLp hxLp))
  rw [hxρ] at h1
  exact absurd h1 (by decide)

theorem no_line {l : Subgroup G} (hZl : V ⊓ centralizer (L : Set G) ≤ l) (hlV : l ≤ V)
    (hl8 : Nat.card l = 8) (hN : Lp ≤ normalizer (l : Set G)) : False := by
  classical
  set Y : Finset P6 := Finset.univ.filter (fun x : P6 => ∃ h : x ∈ G6.coreMod 6,
    ((S.frame.ψ.symm ⟨x, h⟩ : ↥V) : G) ∈ l) with hYdef
  have hmemY : ∀ x : P6, x ∈ Y ↔ ∃ h : x ∈ G6.coreMod 6,
      ((S.frame.ψ.symm ⟨x, h⟩ : ↥V) : G) ∈ l := by
    intro x
    rw [hYdef, Finset.mem_filter]
    simp
  have hY : ∀ w (hw : w ∈ l), (S.frame.ψ ⟨w, hlV hw⟩ : P6) ∈ Y := by
    intro w hw
    refine (hmemY _).2 ⟨(S.frame.ψ ⟨w, hlV hw⟩).2, ?_⟩
    rw [Subtype.coe_eta, MulEquiv.symm_apply_apply]
    exact hw
  have hcard : Y.card = 8 := by
    have e : ↥l ≃ {x // x ∈ Y} :=
      { toFun := fun w => ⟨S.frame.ψ ⟨w, hlV w.2⟩, hY w w.2⟩
        invFun := fun x => ⟨_, ((hmemY x.1).1 x.2).2⟩
        left_inv := fun w => by
          apply Subtype.ext
          show ((S.frame.ψ.symm ⟨(S.frame.ψ ⟨w, hlV w.2⟩ : P6), _⟩ : ↥V) : G) = w
          rw [Subtype.coe_eta, MulEquiv.symm_apply_apply]
        right_inv := fun x => by
          apply Subtype.ext
          show ((S.frame.ψ ⟨_, hlV ((hmemY x.1).1 x.2).2⟩ : ↥(G6.coreMod 6)) : P6) = x
          have : (⟨_, hlV ((hmemY x.1).1 x.2).2⟩ : ↥V) =
              S.frame.ψ.symm ⟨x.1, ((hmemY x.1).1 x.2).1⟩ := rfl
          rw [this, MulEquiv.apply_symm_apply] }
    rw [← hl8, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hYsum : ∀ x ∈ Y, ∑ i, Multiplicative.toAdd x i = 0 := fun x hx =>
    G6.mem_coreMod.1 ((hmemY x).1 hx).1
  have hY1 : (1 : P6) ∈ Y := by
    have := hY 1 (one_mem l)
    rwa [show (⟨1, hlV (one_mem l)⟩ : ↥V) = 1 from rfl, map_one] at this
  have hYe : G6.allOnes 6 ∈ Y := by
    have hz : S.zV ∈ l := hZl ⟨S.zV_mem_V, (S.mem_centralizer_L_iff ⟨_, S.zV_mem_V⟩).2
      (Or.inr rfl)⟩
    have := hY _ hz
    rwa [S.psi_zV] at this
  have hYmul : ∀ x ∈ Y, ∀ y ∈ Y, x * y ∈ Y := by
    intro x hx y hy
    obtain ⟨hx0, hxl⟩ := (hmemY x).1 hx
    obtain ⟨hy0, hyl⟩ := (hmemY y).1 hy
    have h := hY _ (mul_mem hxl hyl)
    have e : (⟨((S.frame.ψ.symm ⟨x, hx0⟩ : ↥V) : G) * ((S.frame.ψ.symm ⟨y, hy0⟩ : ↥V) : G),
        hlV (mul_mem hxl hyl)⟩ : ↥V) = S.frame.ψ.symm ⟨x, hx0⟩ * S.frame.ψ.symm ⟨y, hy0⟩ := rfl
    rw [e, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
    exact h
  have hact : ∀ x : ↥(normalizer (V : Set G)), (x : G) ∈ Lp →
      ∀ y ∈ Y, G6.permAct 6 (S.frame.ρ x) y ∈ Y := by
    intro x hx y hy
    obtain ⟨hy0, hyl⟩ := (hmemY y).1 hy
    set w : ↥V := S.frame.ψ.symm ⟨y, hy0⟩ with hw
    have hxw : (x : G) * w * (x : G)⁻¹ ∈ l := (mem_normalizer_iff.mp (hN hx) w).mp hyl
    have h := hY _ hxw
    have e := S.psi_conj x w
    have e' : (⟨(x : G) * w * (x : G)⁻¹, hlV hxw⟩ : ↥V) =
        ⟨(x : G) * w * (x : G)⁻¹, (mem_normalizer_iff.mp x.2 w).mp w.2⟩ := rfl
    rw [e', e, hw, MulEquiv.apply_symm_apply, G6.coreAct_coe] at h
    exact h
  obtain ⟨x₁, hx₁, hρ₁⟩ := P.three c012 (by decide)
  obtain ⟨x₂, hx₂, hρ₂⟩ := P.three c123 (by decide)
  obtain ⟨a, haY, ha⟩ : ∃ a ∈ Y, a ∉ ({1, G6.allOnes 6} : Finset P6) := by
    by_contra h
    push Not at h
    have := Finset.card_le_card (show Y ⊆ {1, G6.allOnes 6} from fun x hx => h x hx)
    have h2 : ({1, G6.allOnes 6} : Finset P6).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨b, hbY, hb⟩ : ∃ b ∈ Y, b ∉ ({1, G6.allOnes 6, a, a * G6.allOnes 6} : Finset P6) := by
    by_contra h
    push Not at h
    have := Finset.card_le_card
      (show Y ⊆ {1, G6.allOnes 6, a, a * G6.allOnes 6} from fun x hx => h x hx)
    have h4 : ({1, G6.allOnes 6, a, a * G6.allOnes 6} : Finset P6).card ≤ 4 := Finset.card_le_four
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb
  have hind : Indep8 a b := ⟨ha.1, ha.2, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩
  have hsub : span8 a b ⊆ Y := by
    intro x hx
    simp only [span8, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hY1
    · exact hYe
    · exact haY
    · exact hYmul _ haY _ hYe
    · exact hbY
    · exact hYmul _ hbY _ hYe
    · exact hYmul _ haY _ hbY
    · exact hYmul _ (hYmul _ haY _ hbY) _ hYe
  have hYeq : span8 a b = Y :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [hcard, (line8_all a b (hYsum a haY) (hYsum b hbY) hind).1])
  refine (line8_all a b (hYsum a haY) (hYsum b hbY) hind).2 ⟨?_, ?_, ?_, ?_⟩ <;> rw [hYeq]
  · rw [← hρ₁]; exact hact x₁ hx₁ a haY
  · rw [← hρ₁]; exact hact x₁ hx₁ b hbY
  · rw [← hρ₂]; exact hact x₂ hx₂ a haY
  · rw [← hρ₂]; exact hact x₂ hx₂ b hbY

end S134Plus

end CFSG.Quasithin.H13.U3
