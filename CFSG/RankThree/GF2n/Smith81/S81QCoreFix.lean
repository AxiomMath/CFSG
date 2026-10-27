module

public import CFSG.RankThree.GF2n.Smith81.S81QRDLink
public import CFSG.RankThree.GF2n.Smith81.S81XD6Geom
public import CFSG.RankThree.GF2n.Smith81.S81QGen

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81V

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

@[expose] def RootDatum.uRange (R : RootDatum K Γ) : Subgroup Γ where
  carrier := Set.range R.u
  mul_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, R.u_add n m⟩
  one_mem' := by
    refine ⟨0, ?_⟩
    have h := R.u_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := R.u 0) (by rw [mul_one]; exact h.symm)
  inv_mem' := by
    rintro _ ⟨n, rfl⟩
    refine ⟨-n, ?_⟩
    have h := R.u_add n (-n)
    rw [add_neg_cancel] at h
    have h0 : R.u 0 = 1 := by
      have h0' := R.u_add 0 0
      rw [add_zero] at h0'
      exact mul_left_cancel (a := R.u 0) (by rw [mul_one]; exact h0'.symm)
    rw [h0] at h
    exact eq_inv_of_mul_eq_one_right h.symm

theorem RootDatum.closure_range_u_eq_uRange (R : RootDatum K Γ) :
    Subgroup.closure (Set.range R.u) = R.uRange :=
  Subgroup.closure_eq R.uRange

end CFSG.RankThree.GF2n.Smith81.S81V

namespace CFSG.RankThree.GF2n.Smith81.D6Spin

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z CFSG.RankThree.GF2n.Smith81.D6X
  CFSG.RankThree.GF2n.Smith81.S81V
open scoped commutatorElement

section Fix

variable {K : Type} [Field K] [CharP K 2] [Finite K] {X : Type} [AddCommGroup X] [Module K X]
  (A : ↥(EAut0 K) →* (X ≃ₗ[K] X))

@[expose] def fix0 : Submodule K X where
  carrier := {v | ∀ u : ↥(EAut0 K), (u : W K ≃ₗ[K] W K) ∈ rootRad0 K → A u v = v}
  add_mem' {v w} hv hw u hu := by rw [map_add, hv u hu, hw u hu]
  zero_mem' u _ := map_zero _
  smul_mem' c v hv u hu := by rw [map_smul, hv u hu]

theorem mem_fix0 {v : X} :
    v ∈ fix0 A ↔ ∀ u : ↥(EAut0 K), (u : W K ≃ₗ[K] W K) ∈ rootRad0 K → A u v = v := Iff.rfl

@[expose] def V1_0 (β : X →ₗ[K] X →ₗ[K] K) : Submodule K X where
  carrier := {w | (∀ v ∈ fix0 A, β v w = 0) ∧
    ∀ u : ↥(EAut0 K), (u : W K ≃ₗ[K] W K) ∈ rootRad0 K → A u w - w ∈ fix0 A}
  add_mem' {w w'} hw hw' := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_add, hw.1 v hv, hw'.1 v hv, add_zero]
    · have : A u (w + w') - (w + w') = (A u w - w) + (A u w' - w') := by rw [map_add]; abel
      rw [this]
      exact (fix0 A).add_mem (hw.2 u hu) (hw'.2 u hu)
  zero_mem' := ⟨fun v _ => by simp, fun u _ => by simp⟩
  smul_mem' c w hw := by
    refine ⟨fun v hv => ?_, fun u hu => ?_⟩
    · rw [map_smul, hw.1 v hv, smul_zero]
    · have : A u (c • w) - c • w = c • (A u w - w) := by rw [map_smul, smul_sub]
      rw [this]
      exact (fix0 A).smul_mem c (hw.2 u hu)

theorem mem_V1_0 {β : X →ₗ[K] X →ₗ[K] K} {w : X} :
    w ∈ V1_0 A β ↔ (∀ v ∈ fix0 A, β v w = 0) ∧
      ∀ u : ↥(EAut0 K), (u : W K ≃ₗ[K] W K) ∈ rootRad0 K → A u w - w ∈ fix0 A := Iff.rfl

theorem exists_u_of_mem_rootRad0 {x : ↥(EAut0 K)} (hx : (x : W K ≃ₗ[K] W K) ∈ rootRad0 K) :
    ∃ n, (d6RootDatum K).u n = x := by
  have h : x ∈ Subgroup.closure (Set.range (d6RootDatum K).u) := by
    rw [closure_range_u]
    exact hx
  rw [(d6RootDatum K).closure_range_u_eq_uRange] at h
  exact h

theorem toRankOne_fix_eq0 : ((d6RootDatum K).toRankOne A).fix = fix0 A := by
  ext v
  rw [RankOneData.mem_fix, mem_fix0]
  constructor
  · intro h u hu
    obtain ⟨n, rfl⟩ := exists_u_of_mem_rootRad0 hu
    exact h n
  · intro h n
    exact h _ (u_mem_rootRad0 n)

theorem toRankOne_V1_eq0 (β : X →ₗ[K] X →ₗ[K] K) :
    ((d6RootDatum K).toRankOne A).V1 β = V1_0 A β := by
  ext w
  rw [RankOneData.mem_V1, mem_V1_0, toRankOne_fix_eq0]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun u hu => ?_⟩
    obtain ⟨n, rfl⟩ := exists_u_of_mem_rootRad0 hu
    exact h2 n
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun n => h2 _ (u_mem_rootRad0 n)⟩

theorem conj_mem_rootRad0_of_mem_StabP0 {g : ↥(EAut0 K)} (hg : g ∈ StabP0 K) {x : ↥(EAut0 K)}
    (hx : (x : W K ≃ₗ[K] W K) ∈ rootRad0 K) :
    ((g * x * g⁻¹ : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ∈ rootRad0 K := by
  obtain ⟨c, hc, hw⟩ := hg
  exact conj_rootRad0_of_line g.2 hc hw _ hx

theorem fix0_map_le_of_mem_StabP0 {g : ↥(EAut0 K)} (hg : g ∈ StabP0 K) :
    (fix0 A).map (A g : X →ₗ[K] X) ≤ fix0 A := by
  rintro _ ⟨v, hv, rfl⟩
  rw [mem_fix0]
  intro u hu
  have hc : ((g⁻¹ * u * g⁻¹⁻¹ : ↥(EAut0 K)) : W K ≃ₗ[K] W K) ∈ rootRad0 K :=
    conj_mem_rootRad0_of_mem_StabP0 (inv_mem hg) hu
  rw [inv_inv] at hc
  have hfix : A (g⁻¹ * u * g) v = v := (mem_fix0 A).1 hv _ hc
  have key : A u * A g = A g * A (g⁻¹ * u * g) := by
    rw [← map_mul, ← map_mul]
    exact congrArg A (by group)
  have h2 : A u (A g v) = A g (A (g⁻¹ * u * g) v) := by
    rw [← LinearEquiv.mul_apply (A u) (A g), ← LinearEquiv.mul_apply (A g) (A (g⁻¹ * u * g)), key]
  show A u (A g v) = A g v
  rw [h2, hfix]

theorem fix0_map_le_of_mem_P {g : ↥(EAut0 K)} (hg : g ∈ (d6RootDatum K).P) :
    (fix0 A).map (A g : X →ₗ[K] X) ≤ fix0 A :=
  fix0_map_le_of_mem_StabP0 A (d6_P_le_StabP0 hg)

@[expose] def lineStab0 (L : Submodule K X) : Subgroup ↥(EAut0 K) where
  carrier := {g | (∀ x ∈ L, A g x ∈ L) ∧ ∀ x ∈ L, A g⁻¹ x ∈ L}
  mul_mem' {g h} hg hh := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_mul, LinearEquiv.mul_apply]
      exact hg.1 _ (hh.1 x hx)
    · rw [_root_.mul_inv_rev, map_mul, LinearEquiv.mul_apply]
      exact hh.2 _ (hg.2 x hx)
  one_mem' := by
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [map_one]
      exact hx
    · rw [inv_one, map_one]
      exact hx
  inv_mem' {g} hg := by
    refine ⟨hg.2, fun x hx => ?_⟩
    rw [inv_inv]
    exact hg.1 x hx

theorem mem_lineStab0 {L : Submodule K X} {g : ↥(EAut0 K)} :
    g ∈ lineStab0 A L ↔ (∀ x ∈ L, A g x ∈ L) ∧ ∀ x ∈ L, A g⁻¹ x ∈ L := Iff.rfl

end Fix

section Gen

variable {K : Type} [Field K] [CharP K 2] [Finite K]

@[expose] def XL (β : Rt) (hβ : β ∈ Perp) (c : K) : ↥(LamG K) := ⟨xE β c, xE_mem_LamG hβ c⟩

theorem XL_mem_PΛ {β : Rt} (hβ : β ∈ Perp)
    (h : pr (a0 : Fin e7Data.d) β = 0 ∨ pr (a0 : Fin e7Data.d) β = 1) (c : K) :
    XL β hβ c ∈ PΛ K :=
  xE_mem_linNorm0 hβ h c

theorem lamGEquivEAut0_XL {β : Rt} (hβ : β ∈ Perp) (c : K) :
    lamGEquivEAut0 K (XL β hβ c) =
      ⟨vAut0 K (xuWUnit hβ c), vAut0_xuWUnit_mem_EAut0 hβ c⟩ :=
  Subtype.ext (lamGHom_xE hβ c)

theorem sD_conj_XL_alpha (c : K) :
    XL (-alphaA2) (neg_mem_Perp alphaA2_mem_Perp) c = sD K * XL alphaA2 alphaA2_mem_Perp c * sD K := by
  apply Subtype.ext
  show xE (-alphaA2) c = e7Data_valid.nm K nodeA2 * xE alphaA2 c * e7Data_valid.nm K nodeA2
  rw [sD_conj_xE isRoot_alphaA2 c, alphaA2, reflect_single_self]

theorem neg_mem_Psi0_of_pr {β : Rt} (hβ : β ∈ Perp) (hpr : pr (a0 : Fin e7Data.d) β = -1) :
    -β ∈ Psi0 := by
  refine mem_Psi0.2 ⟨neg_mem_Perp hβ, ?_⟩
  rw [← pr_a0_eq (neg_mem_Perp hβ), pr_neg0, hpr]
  norm_num

theorem pr_zero_root : pr (a0 : Fin e7Data.d) (0 : Rt) = 0 := by
  unfold pr
  simp

theorem XL_mem_of_pr_neg (H : Subgroup ↥(LamG K)) (hP : PΛ K ≤ H) (hs : sD K ∈ H) :
    ∀ (n : ℕ) (β : Rt) (hβ : β ∈ Perp), pr (a0 : Fin e7Data.d) β = -1 → ht (-β) ≤ n →
      ∀ c : K, XL β hβ c ∈ H := by
  intro n
  induction n with
  | zero =>
    intro β hβ hpr hle c
    exfalso
    have := ht_pos_Psi0 (neg_mem_Psi0_of_pr hβ hpr)
    simp only [Nat.cast_zero] at hle
    omega
  | succ n ih =>
    intro β hβ hpr hle c
    have hψ : -β ∈ Psi0 := neg_mem_Psi0_of_pr hβ hpr
    by_cases hlow : ht (-β) ≤ n
    · exact ih β hβ hpr hlow c
    by_cases hb : -β = alphaA2
    · have hβ' : β = -alphaA2 := by rw [← hb, neg_neg]
      subst hβ'
      rw [show XL (-alphaA2) hβ c = sD K * XL alphaA2 alphaA2_mem_Perp c * sD K from sD_conj_XL_alpha c]
      exact mul_mem (mul_mem hs (hP (XL_mem_PΛ alphaA2_mem_Perp (Or.inr pr_alphaA2) c))) hs
    · have hP0 := mem_Psi0.1 hψ
      have hP' := perp_iff.1 hP0.1
      obtain ⟨i, hi, hi1, m, hm⟩ := exists_down_simple0 (-β) hP'.1 hP'.2 hP0.2 hb
      have hγroot : IsRoot .E7 (Pi.single i 1 : Rt) := IsRoot.basis i
      have hγP : (Pi.single i 1 : Rt) ∈ Perp := single_mem_Perp0 i hi1
      have hγpr : pr (a0 : Fin e7Data.d) (Pi.single i 1 : Rt) = 0 := pr_single_ne0 i hi hi1
      have hδroot : IsRoot .E7 (-β - Pi.single i 1) := hm ▸ isRoot_cert0 m
      have hδmem : -β - Pi.single i 1 ∈ Psi0 := by
        refine mem_Psi0.2 ⟨perp_iff.2 ⟨hδroot, ?_⟩, ?_⟩
        · show (-β) node1 - (Pi.single i 1 : Rt) node1 = 0
          rw [hP'.2, Pi.single_eq_of_ne (show node1 ≠ i from fun h => hi1 h.symm), sub_zero]
        · show (-β) nodeA2 - (Pi.single i 1 : Rt) nodeA2 = 1
          rw [hP0.2, Pi.single_eq_of_ne (show nodeA2 ≠ i from fun h => hi h.symm), sub_zero]
      have hδ' : -(-β - (Pi.single i 1 : Rt)) = β + Pi.single i 1 := by abel
      have hβ'P : β + Pi.single i 1 ∈ Perp := by
        rw [← hδ']
        exact neg_mem_Perp (mem_Psi0.1 hδmem).1
      have hβ'pr : pr (a0 : Fin e7Data.d) (β + Pi.single i 1) = -1 := by
        rw [pr_add0, hpr, hγpr]
        norm_num
      have hβ'ht : ht (-(β + Pi.single i 1)) ≤ n := by
        have e : -(β + Pi.single i 1 : Rt) = -β - Pi.single i 1 := by abel
        rw [e, ht_sub_single0]
        push_cast at hle
        omega
      have ih' := ih (β + Pi.single i 1) hβ'P hβ'pr hβ'ht c
      have hα : XL (-(Pi.single i 1 : Rt)) (neg_mem_Perp hγP) 1 ∈ H :=
        hP (XL_mem_PΛ _ (Or.inl (by rw [pr_neg0, hγpr, neg_zero])) 1)
      have hβ0 : β ≠ 0 := by
        intro h0
        rw [h0, pr_zero_root] at hpr
        norm_num at hpr
      have hne : (β + Pi.single i 1 : Rt) + -(Pi.single i 1 : Rt) ≠ 0 := by
        rw [add_neg_cancel_right]
        exact hβ0
      have hsum : (β + Pi.single i 1 : Rt) + -(Pi.single i 1 : Rt) = β := add_neg_cancel_right _ _
      have hcomm : (⁅XL (β + Pi.single i 1) hβ'P c, XL (-(Pi.single i 1 : Rt)) (neg_mem_Perp hγP) 1⁆ :
          ↥(LamG K)) = XL β hβ c := by
        apply Subtype.ext
        show ⁅xE (β + Pi.single i 1) c, xE (-(Pi.single i 1 : Rt)) 1⁆ = xE β c
        rw [comm_xE (perp_iff.1 hβ'P).1 (isRoot_neg hγroot) hne c 1,
          if_pos (by rw [hsum]; exact (perp_iff.1 hβ).1), hsum, mul_one]
      rw [← hcomm, commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ih' hα) (inv_mem ih')) (inv_mem hα)

theorem XL_mem_all (H : Subgroup ↥(LamG K)) (hP : PΛ K ≤ H) (hs : sD K ∈ H) {β : Rt}
    (hβ : β ∈ Perp) (c : K) : XL β hβ c ∈ H := by
  have hroot : IsRoot .E7 β := (perp_iff.1 hβ).1
  rcases pr_mem hroot (a0 : Fin e7Data.d) with h | h | h
  · exact XL_mem_of_pr_neg H hP hs (ht (-β)).toNat β hβ h (Int.self_le_toNat _) c
  · exact hP (XL_mem_PΛ hβ (Or.inl h) c)
  · exact hP (XL_mem_PΛ hβ (Or.inr h) c)

theorem closure_P_s0 (H : Subgroup ↥(EAut0 K)) (hP : (d6RootDatum K).P ≤ H)
    (hs : (d6RootDatum K).s ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro g _
  set H' : Subgroup ↥(LamG K) := H.comap (lamGEquivEAut0 K).toMonoidHom with hH'
  have hP' : PΛ K ≤ H' := fun x hx => hP (Subgroup.mem_map_of_mem _ hx)
  have hs' : sD K ∈ H' := hs
  have hgen : ∀ x : W K ≃ₗ[K] W K, x ∈ Subgroup.closure (genSet0 K) →
      ∃ hE : x ∈ EAut0 K, (⟨x, hE⟩ : ↥(EAut0 K)) ∈ H := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β, hβ, c, rfl⟩ := hx
      refine ⟨vAut0_xuWUnit_mem_EAut0 hβ c, ?_⟩
      have h := XL_mem_all H' hP' hs' hβ c
      rw [hH', Subgroup.mem_comap] at h
      rwa [MulEquiv.coe_toMonoidHom, lamGEquivEAut0_XL] at h
    | one => exact ⟨one_mem _, one_mem H⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨hxE, hxH⟩ := ihx
      obtain ⟨hyE, hyH⟩ := ihy
      exact ⟨mul_mem hxE hyE, mul_mem hxH hyH⟩
    | inv x hx ih =>
      obtain ⟨hxE, hxH⟩ := ih
      exact ⟨inv_mem hxE, inv_mem hxH⟩
  have hg : (g : W K ≃ₗ[K] W K) ∈ Subgroup.closure (genSet0 K) := by
    rw [← EAut0_eq_closure_genSet0]
    exact g.2
  obtain ⟨hE, hH⟩ := hgen g.1 hg
  exact hH

variable {X : Type} [AddCommGroup X] [Module K X] [FiniteDimensional K X]

theorem sv_D6 (A : ↥(EAut0 K) →* (X ≃ₗ[K] X)) (hline : Module.finrank K (fix0 A) = 1)
    (hspan : ⨆ g : ↥(EAut0 K), (fix0 A).map (A g : X →ₗ[K] X) = ⊤) (hV : 1 < Module.finrank K X)
    {v₀ : X} (hv₀ : v₀ ∈ fix0 A) (hne : v₀ ≠ 0) : A (d6RootDatum K).s v₀ ∉ fix0 A := by
  intro hs
  have hmul : ∀ x ∈ fix0 A, ∃ c : K, c • v₀ = x := by
    intro x hx
    have hnz : (⟨v₀, hv₀⟩ : ↥(fix0 A)) ≠ 0 := fun h => hne (congrArg Subtype.val h)
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hline hnz ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hlin : ∀ g : ↥(EAut0 K), A g v₀ ∈ fix0 A → ∀ x ∈ fix0 A, A g x ∈ fix0 A := by
    intro g hg x hx
    obtain ⟨c, rfl⟩ := hmul x hx
    rw [map_smul]
    exact (fix0 A).smul_mem c hg
  have hsStab : (d6RootDatum K).s ∈ lineStab0 A (fix0 A) := by
    rw [mem_lineStab0]
    have hsinv : ((d6RootDatum K).s)⁻¹ = (d6RootDatum K).s :=
      inv_eq_of_mul_eq_one_right (d6RootDatum K).s_sq
    rw [hsinv]
    exact ⟨hlin _ hs, hlin _ hs⟩
  have hPle : (d6RootDatum K).P ≤ lineStab0 A (fix0 A) := by
    intro g hg
    rw [mem_lineStab0]
    exact ⟨fun x hx => fix0_map_le_of_mem_P A hg (Submodule.mem_map_of_mem hx),
      fun x hx => fix0_map_le_of_mem_P A (inv_mem hg) (Submodule.mem_map_of_mem hx)⟩
  have hTop : lineStab0 A (fix0 A) = ⊤ := closure_P_s0 _ hPle hsStab
  have hall : ∀ g : ↥(EAut0 K), ∀ x ∈ fix0 A, A g x ∈ fix0 A := by
    intro g
    have hg : g ∈ lineStab0 A (fix0 A) := by
      rw [hTop]
      exact Subgroup.mem_top g
    exact ((mem_lineStab0 A).1 hg).1
  have hle : (⨆ g : ↥(EAut0 K), (fix0 A).map (A g : X →ₗ[K] X)) ≤ fix0 A := by
    refine iSup_le fun g => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hall g x hx
  rw [hspan, top_le_iff] at hle
  rw [hle, finrank_top] at hline
  omega

end Gen

end CFSG.RankThree.GF2n.Smith81.D6Spin
