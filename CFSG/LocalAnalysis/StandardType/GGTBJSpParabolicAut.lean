module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp
public import CFSG.LocalAnalysis.StandardType.GGTBJSpBlockRank
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj

public section

namespace CFSG.StandardType.SpCoord

open Multiplicative

variable {p k : ℕ}

theorem IsSignedPerm.mul {u v : MulAut (Fin k → Multiplicative (ZMod p))}
    (hu : IsSignedPerm u) (hv : IsSignedPerm v) :
    IsSignedPerm (⇑(u * v : MulAut (Fin k → Multiplicative (ZMod p)))) := by
  obtain ⟨πu, εu, hεu, hu⟩ := hu
  obtain ⟨πv, εv, hεv, hv⟩ := hv
  refine ⟨πu * πv, fun i => εu (πv i) * εv i, fun i => ?_, fun f i => ?_⟩
  · rcases hεu (πv i) with h | h <;> rcases hεv i with h' | h' <;> simp [h, h']
  · rw [MulAut.mul_apply, Equiv.Perm.mul_apply, hu, hv, mul_assoc]

theorem IsSignedPerm.inv {u : MulAut (Fin k → Multiplicative (ZMod p))}
    (hu : IsSignedPerm u) :
    IsSignedPerm (⇑(u⁻¹ : MulAut (Fin k → Multiplicative (ZMod p)))) := by
  obtain ⟨π, ε, hε, hu⟩ := hu
  let v : MulAut (Fin k → Multiplicative (ZMod p)) := u.symm
  change IsSignedPerm v
  refine ⟨π.symm, fun i => ε (π.symm i), fun i => hε _, fun f i => ?_⟩
  have h := hu (v f) (π.symm i)
  have huv : u (v f) = f := u.apply_symm_apply f
  rw [huv, π.apply_symm_apply] at h
  calc toAdd (v f (π.symm i)) =
        (ε (π.symm i) * ε (π.symm i)) * toAdd (v f (π.symm i)) := by
          rw [coord_sign_mul_self (hε _), one_mul]
    _ = ε (π.symm i) * (ε (π.symm i) * toAdd (v f (π.symm i))) := mul_assoc _ _ _
    _ = ε (π.symm i) * toAdd (f i) := congrArg (fun z => ε (π.symm i) * z) h.symm

theorem isSignedPerm_diagAut (ε : Fin k → ZMod p) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    IsSignedPerm (⇑(diagAut ε fun i => coord_sign_mul_self (hε i))) := by
  refine ⟨1, ε, hε, fun f i => ?_⟩
  rw [Equiv.Perm.one_apply, diagAut_apply, toAdd_ofAdd]

theorem mem_of_isSignedPerm_fix_first (hp : p.Prime)
    {H : Subgroup (MulAut (Fin 3 → Multiplicative (ZMod p)))}
    (hs₁ : sgnAut (1 : Fin 3) ∈ H) (hs₂ : sgnAut (2 : Fin 3) ∈ H)
    (ht : permAut (Equiv.swap (1 : Fin 3) 2) ∈ H)
    {u : MulAut (Fin 3 → Multiplicative (ZMod p))} (hu : IsSignedPerm u)
    (hfix : u ((Pi.mulSingle (0 : Fin 3) (ofAdd (1 : ZMod p))) :
      Fin 3 → Multiplicative (ZMod p)) =
      (Pi.mulSingle (0 : Fin 3) (ofAdd (1 : ZMod p)) : Fin 3 → Multiplicative (ZMod p))) :
    u ∈ H := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨π, ε, hε, hu⟩ := hu
  have hBasis := (IsSignedPerm.apply_mulSingle hu (0 : Fin 3) (1 : ZMod p)).symm
  rw [hfix, mul_one] at hBasis
  obtain ⟨hπ, hε₀⟩ :=
    mulSingle_ofAdd_eq_iff (coord_sign_ne_zero hp (hε 0)) hBasis
  have hπcases : π = 1 ∨ π = Equiv.swap 1 2 :=
    (by decide +kernel : ∀ π : Equiv.Perm (Fin 3),
      π 0 = 0 → π = 1 ∨ π = Equiv.swap 1 2) π hπ
  have hform : u = permAut π * diagAut ε (fun i => coord_sign_mul_self (hε i)) := by
    apply MulEquiv.ext
    intro f
    apply eq_of_toAdd_perm_eq π
    intro i
    simpa [MulAut.mul_apply, permAut_apply, diagAut_apply] using hu f i
  have hdiag : diagAut ε (fun i => coord_sign_mul_self (hε i)) ∈ H := by
    rcases hε 1 with h₁ | h₁ <;> rcases hε 2 with h₂ | h₂
    · have hD : diagAut ε (fun i => coord_sign_mul_self (hε i)) = 1 := by
        ext f i
        fin_cases i <;> simp [diagAut_apply, hε₀, h₁, h₂]
      rw [hD]
      exact H.one_mem
    · have hD : diagAut ε (fun i => coord_sign_mul_self (hε i)) = sgnAut (2 : Fin 3) := by
        ext f i
        fin_cases i <;> simp [diagAut_apply, sgnAut_apply, hε₀, h₁, h₂]
      rwa [hD]
    · have hD : diagAut ε (fun i => coord_sign_mul_self (hε i)) = sgnAut (1 : Fin 3) := by
        ext f i
        fin_cases i <;> simp [diagAut_apply, sgnAut_apply, hε₀, h₁, h₂]
      rwa [hD]
    · have hD : diagAut ε (fun i => coord_sign_mul_self (hε i)) =
          sgnAut (1 : Fin 3) * sgnAut (2 : Fin 3) := by
        ext f i
        fin_cases i <;> simp [diagAut_apply, sgnAut_apply, MulAut.mul_apply, hε₀, h₁, h₂]
      rw [hD]
      exact H.mul_mem hs₁ hs₂
  rw [hform]
  apply H.mul_mem _ hdiag
  rcases hπcases with h | h
  · rw [h]
    have hOne : (permAut (1 : Equiv.Perm (Fin 3)) :
        MulAut (Fin 3 → Multiplicative (ZMod p))) = 1 := by ext f i; rfl
    rw [hOne]
    exact H.one_mem
  · rwa [h]

theorem mem_of_isSignedPerm_fix_diagonal
    {H : Subgroup (MulAut (Fin 3 → Multiplicative (ZMod p)))}
    (ht₀ : permAut (Equiv.swap (0 : Fin 3) 1) ∈ H)
    (ht₁ : permAut (Equiv.swap (1 : Fin 3) 2) ∈ H)
    {u : MulAut (Fin 3 → Multiplicative (ZMod p))} (hu : IsSignedPerm u)
    (hfix : u (fun _ => ofAdd (1 : ZMod p)) = fun _ => ofAdd (1 : ZMod p)) : u ∈ H := by
  classical
  obtain ⟨π, ε, hε, hu⟩ := hu
  have hε₁ : ∀ i, ε i = 1 := by
    intro i
    have h := hu (fun _ => ofAdd (1 : ZMod p)) i
    simpa only [hfix, toAdd_ofAdd, mul_one] using h.symm
  have hform : u = permAut π := by
    apply MulEquiv.ext
    intro f
    apply eq_of_toAdd_perm_eq π
    intro i
    simpa [permAut_apply, hε₁] using hu f i
  have hT : permAut (Equiv.swap (0 : Fin 3) 2) ∈ H := by
    have hEq : (permAut (Equiv.swap (0 : Fin 3) 2) :
        MulAut (Fin 3 → Multiplicative (ZMod p))) =
        permAut (Equiv.swap 0 1) * permAut (Equiv.swap 1 2) * permAut (Equiv.swap 0 1) := by
      ext f i
      fin_cases i <;> simp [permAut_apply, MulAut.mul_apply, Function.comp_apply, Equiv.swap_inv, Equiv.swap_apply_def]
    rw [hEq]
    exact H.mul_mem (H.mul_mem ht₀ ht₁) ht₀
  have hswaps : ∀ a b : Fin 3, a ≠ b → permAut (Equiv.swap a b) ∈ H := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · exact (hab rfl).elim
    · exact ht₀
    · exact hT
    · rw [Equiv.swap_comm]; exact ht₀
    · exact (hab rfl).elim
    · exact ht₁
    · rw [Equiv.swap_comm]; exact hT
    · rw [Equiv.swap_comm]; exact ht₁
    · exact (hab rfl).elim
  have hperm : ∀ π : Equiv.Perm (Fin 3), permAut π ∈ H := by
    intro π
    induction π using Equiv.Perm.swap_induction_on with
    | one =>
      have hOne : (permAut (1 : Equiv.Perm (Fin 3)) :
          MulAut (Fin 3 → Multiplicative (ZMod p))) = 1 := by ext f i; rfl
      rw [hOne]
      exact H.one_mem
    | swap_mul π a b hab ih =>
      have hEq : (permAut (Equiv.swap a b * π) :
          MulAut (Fin 3 → Multiplicative (ZMod p))) = permAut (Equiv.swap a b) * permAut π := by
        ext f i
        simp [permAut_apply, MulAut.mul_apply, Function.comp_apply, Equiv.Perm.mul_apply]
      rw [hEq]
      exact H.mul_mem (hswaps a b hab) ih
  rw [hform]
  exact hperm π

theorem eq_closure_pair_of_fix_first (hp : p.Prime)
    (H : Subgroup (MulAut (Fin 3 → Multiplicative (ZMod p))))
    (hH : ∀ u ∈ H, IsSignedPerm u)
    (hfix : ∀ u ∈ H, u ((Pi.mulSingle (0 : Fin 3) (ofAdd (1 : ZMod p))) :
      Fin 3 → Multiplicative (ZMod p)) = Pi.mulSingle (0 : Fin 3) (ofAdd (1 : ZMod p)))
    (hs : sgnAut (2 : Fin 3) ∈ H) (ht : permAut (Equiv.swap (1 : Fin 3) 2) ∈ H) :
    H = Subgroup.closure ({sgnAut (2 : Fin 3), permAut (Equiv.swap (1 : Fin 3) 2)} :
      Set (MulAut (Fin 3 → Multiplicative (ZMod p)))) := by
  let C := Subgroup.closure ({sgnAut (2 : Fin 3), permAut (Equiv.swap (1 : Fin 3) 2)} :
    Set (MulAut (Fin 3 → Multiplicative (ZMod p))))
  have hsC : sgnAut (2 : Fin 3) ∈ C := Subgroup.subset_closure (by simp)
  have htC : permAut (Equiv.swap (1 : Fin 3) 2) ∈ C := Subgroup.subset_closure (by simp)
  have hs₁C : sgnAut (1 : Fin 3) ∈ C := by
    have hact : ∀ f i, toAdd (permAut (Equiv.swap (1 : Fin 3) 2) f
        ((Equiv.swap (1 : Fin 3) 2) i)) = (1 : ZMod p) * toAdd (f i) := by
      intro f i
      simp [permAut_apply]
    have hcomm := IsSignedPerm.mul_sgnAut (u := permAut (Equiv.swap (1 : Fin 3) 2))
      (π := Equiv.swap (1 : Fin 3) 2) (ε := fun _ => (1 : ZMod p)) hact (2 : Fin 3)
    have heq : permAut (Equiv.swap (1 : Fin 3) 2) * sgnAut (2 : Fin 3) *
        (permAut (Equiv.swap (1 : Fin 3) 2) : MulAut (Fin 3 → Multiplicative (ZMod p)))⁻¹ =
        sgnAut (1 : Fin 3) := by
      rw [hcomm]
      simp only [Equiv.swap_apply_right, mul_inv_cancel_right]
    have h := C.mul_mem (C.mul_mem htC hsC) (C.inv_mem htC)
    rwa [heq] at h
  apply le_antisymm
  · intro u hu
    exact mem_of_isSignedPerm_fix_first hp hs₁C hsC htC (hH u hu) (hfix u hu)
  · rw [Subgroup.closure_le]
    intro u hu
    rcases Set.mem_insert_iff.mp hu with h | h
    · simpa [h] using hs
    · simpa [Set.mem_singleton_iff.mp h] using ht

theorem eq_closure_pair_of_fix_diagonal
    (H : Subgroup (MulAut (Fin 3 → Multiplicative (ZMod p))))
    (hH : ∀ u ∈ H, IsSignedPerm u)
    (hfix : ∀ u ∈ H, u (fun _ => ofAdd (1 : ZMod p)) = fun _ => ofAdd (1 : ZMod p))
    (ht₀ : permAut (Equiv.swap (0 : Fin 3) 1) ∈ H)
    (ht₁ : permAut (Equiv.swap (1 : Fin 3) 2) ∈ H) :
    H = Subgroup.closure ({permAut (Equiv.swap (0 : Fin 3) 1),
      permAut (Equiv.swap (1 : Fin 3) 2)} : Set (MulAut (Fin 3 → Multiplicative (ZMod p)))) := by
  let C := Subgroup.closure ({permAut (Equiv.swap (0 : Fin 3) 1),
    permAut (Equiv.swap (1 : Fin 3) 2)} : Set (MulAut (Fin 3 → Multiplicative (ZMod p))))
  have ht₀C : permAut (Equiv.swap (0 : Fin 3) 1) ∈ C := Subgroup.subset_closure (by simp)
  have ht₁C : permAut (Equiv.swap (1 : Fin 3) 2) ∈ C := Subgroup.subset_closure (by simp)
  apply le_antisymm
  · intro u hu
    exact mem_of_isSignedPerm_fix_diagonal ht₀C ht₁C (hH u hu) (hfix u hu)
  · rw [Subgroup.closure_le]
    intro u hu
    rcases Set.mem_insert_iff.mp hu with h | h
    · simpa [h] using ht₀
    · simpa [Set.mem_singleton_iff.mp h] using ht₁

end CFSG.StandardType.SpCoord

namespace CFSG.StandardType

open CFSG.Open (StatedSp)
open TableBSymp SpCoord Multiplicative

theorem ggTBJSpC_diagAut_conj_reflAut {p m : ℕ} {α : Type*}
    (t : Fin m → α) (a b : α) (ε : Fin m → ZMod p)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (ht : ∀ i, t i = a ∨ t i = b)
    (htε : ∀ i, (t i = a → ε i = 1) ∧ (t i = b → ε i = -1))
    {u w : Fin m} (huw : u ≠ w) :
    diagAut ε (fun i => coord_sign_mul_self (hε i)) * permAut (Equiv.swap u w) *
        (diagAut ε (fun i => coord_sign_mul_self (hε i)))⁻¹ =
      ggTBJSpC_reflAut p m t u w := by
  classical
  have hdata : ∀ f i, toAdd
      (diagAut ε (fun i => coord_sign_mul_self (hε i)) f ((1 : Equiv.Perm (Fin m)) i)) =
      ε i * toAdd (f i) := by
    intro f i
    simp [diagAut_apply]
  by_cases h : t u = t w
  · have hs : ε u * ε w = 1 := by
      rcases ht u with hu | hu
      · rw [(htε u).1 hu, (htε w).1 (h.symm.trans hu), one_mul]
      · rw [(htε u).2 hu, (htε w).2 (h.symm.trans hu)]
        ring
    rw [ggTBJSpC_reflAut, if_pos h]
    simpa only [Equiv.Perm.one_apply] using
      conj_permAut_swap_eq_of_mul_eq_one hε hdata hs
  · have hs : ε u * ε w = -1 := by
      rcases ht u with hu | hu <;> rcases ht w with hw | hw
      · exact (h (hu.trans hw.symm)).elim
      · rw [(htε u).1 hu, (htε w).2 hw, one_mul]
      · rw [(htε u).2 hu, (htε w).1 hw, mul_one]
      · exact (h (hu.trans hw.symm)).elim
    rw [ggTBJSpC_reflAut, if_neg h, ggTBJSpC_invSwapAut_eq_sgnAut_conj]
    simpa only [Equiv.Perm.one_apply] using
      conj_permAut_swap_eq_of_mul_eq_neg_one hε hdata huw hs

theorem mem_map_congr_ggAutomizer_iff {G : Type} {C : Type*} [Group G] [Finite G] [Group C]
    (E J : Subgroup G) (κ : C ≃* E) (u : MulAut C) :
    u ∈ (ggAutomizer J E).map (MulAut.congr κ.symm).toMonoidHom ↔
      ∃ g ∈ J, ∀ c, g * (κ c : G) * g⁻¹ = (κ (u c) : G) := by
  constructor
  · intro hu
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨g, hg, _hgN, hga⟩ := mem_ggAutomizer_iff.mp ha
    refine ⟨g, hg, fun c => ?_⟩
    simpa [MulAut.congr_apply] using (hga (κ c)).symm
  · rintro ⟨g, hg, hact⟩
    have hgN : g ∈ Subgroup.normalizer (E : Set G) := by
      refine mem_normalizer_of_forall_conj_mem fun e he => ?_
      obtain ⟨c, hc⟩ := κ.surjective ⟨e, he⟩
      have hpre := hact (u.symm c)
      rw [u.apply_symm_apply] at hpre
      have hce : (κ c : G) = e := congrArg Subtype.val hc
      rw [hce] at hpre
      have heq : g⁻¹ * e * g = (κ (u.symm c) : G) := by
        rw [← hpre]
        group
      rw [heq]
      exact (κ (u.symm c)).2
    refine Subgroup.mem_map.mpr ⟨ggConjAut E hgN, ggConjAut_mem_ggAutomizer hg hgN, ?_⟩
    apply MulEquiv.ext
    intro c
    apply κ.injective
    apply Subtype.ext
    simpa [MulAut.congr_apply, ggConjAut_apply] using hact c

theorem TableBSymp.spTorusSp_injective {p m : ℕ} [NeZero p]
    {K : Type} [Field K] {ζ : Kˣ} (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) :
    Function.Injective (spTorusSp (m := m) hζ) := by
  intro f f' hff
  funext i
  apply ReflSp.zmodPowHom_injective hζ hζo
  apply Units.ext
  have h := congrArg (fun g : CFSG.Assembly.LargeEvenSpGroup K m =>
    ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (.inl i) (.inl i)) hff
  simpa only [spTorusSp_coe, spTorusGL_apply, TauCeti.diagGL_coe,
    Matrix.diagonal_apply, pairedUnits, Sum.elim_inl, ite_true] using h

theorem ggTBJ_sp_isSignedPerm_of_torus_conj {p m : ℕ} (hp : p.Prime)
    {K : Type} [Field K] {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (g : GL (Fin m ⊕ Fin m) K) (u : MulAut (Fin m → Multiplicative (ZMod p)))
    (hu : ∀ f, g * spTorusGL hζ f * g⁻¹ = spTorusGL hζ (u f)) :
    SpCoord.IsSignedPerm u := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨j, ε, hε, hj⟩ := ReflSp.exists_monomial_data hζo hζ g
  have hrel : ∀ f, g * spTorusGL hζ f = spTorusGL hζ (u f) * g := by
    intro f
    calc g * spTorusGL hζ f = (g * spTorusGL hζ f * g⁻¹) * g := by group
      _ = spTorusGL hζ (u f) * g := by rw [hu f]
  have haction : ∀ f i, toAdd (u f (j i)) = ε i * toAdd (f i) :=
    fun f i => hj f (u f) (hrel f) i
  have hjinj : Function.Injective j := by
    intro i i' hii
    by_contra hne
    let f : Fin m → Multiplicative (ZMod p) := Pi.mulSingle i (ofAdd (1 : ZMod p))
    have h₁ := haction f i
    have h₂ := haction f i'
    rw [← hii, h₁, toAdd_mulSingle, toAdd_mulSingle,
      ite_eq_left rfl, ite_eq_right (Ne.symm hne), mul_one, mul_zero] at h₂
    exact coord_sign_ne_zero hp (hε i) h₂
  exact ⟨Equiv.ofBijective j hjinj.bijective_of_finite, ε, hε, haction⟩

theorem ggTBJ_sp_torus_automizer_signed {p m : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (J : Subgroup (CFSG.Assembly.LargeEvenSpGroup K m))
    (κ : (Fin m → Multiplicative (ZMod p)) ≃* (spTorusSp (m := m) hζ).range)
    (hκ : ∀ f, (κ f : CFSG.Assembly.LargeEvenSpGroup K m) = spTorusSp hζ f)
    {u : MulAut (Fin m → Multiplicative (ZMod p))}
    (hu : u ∈ (ggAutomizer J (spTorusSp (m := m) hζ).range).map
      (MulAut.congr κ.symm).toMonoidHom) : SpCoord.IsSignedPerm u := by
  obtain ⟨g, _hg, hact⟩ := (mem_map_congr_ggAutomizer_iff _ J κ u).mp hu
  apply ggTBJ_sp_isSignedPerm_of_torus_conj hp hζo hζ (g : GL (Fin m ⊕ Fin m) K) u
  intro f
  have h := hact f
  rw [hκ f, hκ (u f)] at h
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe]
    using congrArg (fun g : CFSG.Assembly.LargeEvenSpGroup K m =>
      (g : GL (Fin m ⊕ Fin m) K)) h

theorem ggTBJ_sp_torus_automizer_signed_of_coordinates {p m : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (J : Subgroup (CFSG.Assembly.LargeEvenSpGroup K m))
    (q : MulAut (Fin m → Multiplicative (ZMod p))) (hq : SpCoord.IsSignedPerm q)
    (κ : (Fin m → Multiplicative (ZMod p)) ≃* (spTorusSp (m := m) hζ).range)
    (hκ : ∀ f, (κ f : CFSG.Assembly.LargeEvenSpGroup K m) = spTorusSp hζ (q f))
    {u : MulAut (Fin m → Multiplicative (ZMod p))}
    (hu : u ∈ (ggAutomizer J (spTorusSp (m := m) hζ).range).map
      (MulAut.congr κ.symm).toMonoidHom) : SpCoord.IsSignedPerm u := by
  obtain ⟨g, _hg, hact⟩ := (mem_map_congr_ggAutomizer_iff _ J κ u).mp hu
  let v : MulAut (Fin m → Multiplicative (ZMod p)) := q * u * q⁻¹
  have hconj : ∀ f, (g : GL (Fin m ⊕ Fin m) K) * spTorusGL hζ f *
      (g : GL (Fin m ⊕ Fin m) K)⁻¹ = spTorusGL hζ (v f) := by
    intro f
    have h := hact (q.symm f)
    rw [hκ (q.symm f), hκ (u (q.symm f)), q.apply_symm_apply] at h
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, spTorusSp_coe, v, MulAut.mul_apply]
      using congrArg (fun g : CFSG.Assembly.LargeEvenSpGroup K m =>
        (g : GL (Fin m ⊕ Fin m) K)) h
  have hv := ggTBJ_sp_isSignedPerm_of_torus_conj hp hζo hζ _ v hconj
  have hback : (q⁻¹ * v * q : MulAut (Fin m → Multiplicative (ZMod p))) = u := by
    dsimp [v]
    group
  exact hback ▸ (hq.inv.mul (hv.mul hq))

theorem ggTBJ_sp_zero_block_automizer {p : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (t : Fin 3 → Kˣ) (σ : Equiv.Perm (Fin 3))
    (ht₀ : t (σ 0) ≠ 1) (ht₁ : t (σ 1) = 1) (ht₂ : t (σ 2) = 1)
    {J : Subgroup (CFSG.Assembly.LargeEvenSpGroup K 3)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({CFSG.SeitzReduction.SymplecticPilot.diagSp K 3 t} :
        Set (CFSG.Assembly.LargeEvenSpGroup K 3))))
    (hcount : p ^ 2 * Nat.card {f : Fin 3 → Multiplicative (ZMod p) //
      ∀ j ∈ J, spTorusSp hζ f * j = j * spTorusSp hζ f} ≤ p ^ 3)
    (κ : (Fin 3 → Multiplicative (ZMod p)) ≃* (spTorusSp (m := 3) hζ).range)
    (hκ : ∀ f, (κ f : CFSG.Assembly.LargeEvenSpGroup K 3) =
      spTorusSp hζ (permAut σ f)) :
    (ggAutomizer J (spTorusSp (m := 3) hζ).range).map (MulAut.congr κ.symm).toMonoidHom =
      Subgroup.closure ({sgnAut (2 : Fin 3), permAut (Equiv.swap (1 : Fin 3) 2)} :
        Set (MulAut (Fin 3 → Multiplicative (ZMod p)))) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨lam, hperm, _hmixed, hsign, hcentral, hcase⟩ :=
    ggTBJ_sp_blockData_rank_three hp hK4 hζ t ⟨σ 0, ht₀⟩ hJ hcount
  have hlam : lam = 1 := by
    rcases hcase with ⟨h, _⟩ | ⟨h, hcover⟩
    · exact h
    · have h₁ := hcover (σ 1)
      rw [ht₁] at h₁
      rcases h₁ with h₁ | h₁
      · exact (h h₁.symm).elim
      · exact (h (inv_eq_one.mp h₁.symm)).elim
  let H := (ggAutomizer J (spTorusSp (m := 3) hζ).range).map
    (MulAut.congr κ.symm).toMonoidHom
  have hq : IsSignedPerm (⇑(permAut σ : MulAut (Fin 3 → Multiplicative (ZMod p)))) :=
    ⟨σ, fun _ => 1, fun _ => Or.inl rfl, fun f i => by simp [permAut_apply]⟩
  apply SpCoord.eq_closure_pair_of_fix_first hp H
  · intro u hu
    exact ggTBJ_sp_torus_automizer_signed_of_coordinates hp hζo hζ J
      (permAut σ) hq κ hκ hu
  · intro u hu
    obtain ⟨n, hn, hact⟩ := (mem_map_congr_ggAutomizer_iff _ J κ u).mp hu
    let δ : Fin 3 → Multiplicative (ZMod p) := Pi.mulSingle (0 : Fin 3) (ofAdd (1 : ZMod p))
    have hx : ∀ i, t i = 1 → zmodPowHom hζ (permAut σ δ i) = 1 := by
      intro i hi
      have hi₀ : i ≠ σ 0 := by intro h; rw [h] at hi; exact ht₀ hi
      simp [δ, permAut_mulSingle, Pi.mulSingle_apply, hi₀]
    have hc := hcentral (fun i => zmodPowHom hζ (permAut σ δ i))
      (Or.inl ⟨hlam, hx⟩) n hn
    have hc' : spTorusSp hζ (permAut σ δ) * n = n * spTorusSp hζ (permAut σ δ) := by
      simpa only [ggTBJSpC_spTorusSp_eq_diagSp hζ (permAut σ δ)] using hc
    change u δ = δ
    apply κ.injective
    apply Subtype.ext
    have h := hact δ
    rw [hκ δ, hκ (u δ)] at h
    rw [hκ (u δ), hκ δ]
    calc spTorusSp hζ (permAut σ (u δ)) =
        n * spTorusSp hζ (permAut σ δ) * n⁻¹ := h.symm
      _ = spTorusSp hζ (permAut σ δ) := by rw [← hc']; group
  · refine (mem_map_congr_ggAutomizer_iff _ J κ (sgnAut (2 : Fin 3))).mpr
      ⟨spSwapSp (σ 2), hsign hlam (σ 2) ht₂, ?_⟩
    intro f
    have hcov := IsSignedPerm.mul_sgnAut (p := p) (u := permAut σ)
      (π := σ) (ε := fun _ => 1) (fun f i => by simp [permAut_apply]) (2 : Fin 3)
    have hqsgn : permAut σ (sgnAut (2 : Fin 3) f) = sgnAut (σ 2) (permAut σ f) := by
      simpa only [MulAut.mul_apply] using congrArg (fun v : MulAut _ => v f) hcov
    rw [hκ f, hκ (sgnAut (2 : Fin 3) f)]
    rw [hqsgn]
    exact ggTBJSpC_conj_spSwapSp hζ (σ 2) (permAut σ f)
  · refine (mem_map_congr_ggAutomizer_iff _ J κ (permAut (Equiv.swap (1 : Fin 3) 2))).mpr
      ⟨CFSG.SeitzReduction.SymplecticPilot.permSp K (Equiv.swap (σ 1) (σ 2)),
        hperm (σ 1) (σ 2) (fun h => (by decide : (1 : Fin 3) ≠ 2) (σ.injective h))
          (ht₁.trans ht₂.symm) (Or.inl (ht₁.trans hlam.symm)), ?_⟩
    intro f
    have hcov : (permAut σ : MulAut (Fin 3 → Multiplicative (ZMod p))) *
        permAut (Equiv.swap (1 : Fin 3) 2) =
        permAut (Equiv.swap (σ 1) (σ 2)) * permAut σ := by
      have h := congrArg (fun v : MulAut _ => v * permAut σ)
        (permAut_conj_swap (p := p) σ (1 : Fin 3) 2)
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
    have hqperm : permAut σ (permAut (Equiv.swap (1 : Fin 3) 2) f) =
        permAut (Equiv.swap (σ 1) (σ 2)) (permAut σ f) := by
      simpa only [MulAut.mul_apply] using congrArg (fun v : MulAut _ => v f) hcov
    rw [hκ f, hκ (permAut (Equiv.swap (1 : Fin 3) 2) f)]
    rw [hqperm]
    exact ggTBJSpC_conj_permSp hζ (Equiv.swap (σ 1) (σ 2)) (permAut σ f)

theorem ggTBJ_sp_paired_block_automizer {p : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (t : Fin 3 → Kˣ) (a : Kˣ) (ha : a ≠ 1) (hta : ∀ i, t i = a ∨ t i = a⁻¹)
    (ε : Fin 3 → ZMod p) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (htε : ∀ i, (t i = a → ε i = 1) ∧ (t i = a⁻¹ → ε i = -1))
    {J : Subgroup (CFSG.Assembly.LargeEvenSpGroup K 3)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({CFSG.SeitzReduction.SymplecticPilot.diagSp K 3 t} :
        Set (CFSG.Assembly.LargeEvenSpGroup K 3))))
    (hcount : p ^ 2 * Nat.card {f : Fin 3 → Multiplicative (ZMod p) //
      ∀ j ∈ J, spTorusSp hζ f * j = j * spTorusSp hζ f} ≤ p ^ 3)
    (κ : (Fin 3 → Multiplicative (ZMod p)) ≃* (spTorusSp (m := 3) hζ).range)
    (hκ : ∀ f, (κ f : CFSG.Assembly.LargeEvenSpGroup K 3) =
      spTorusSp hζ (diagAut ε (fun i => coord_sign_mul_self (hε i)) f)) :
    (ggAutomizer J (spTorusSp (m := 3) hζ).range).map (MulAut.congr κ.symm).toMonoidHom =
      Subgroup.closure ({permAut (Equiv.swap (0 : Fin 3) 1),
        permAut (Equiv.swap (1 : Fin 3) 2)} : Set (MulAut (Fin 3 → Multiplicative (ZMod p)))) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have htn : ∀ i, t i ≠ 1 := by
    intro i hi
    rcases hta i with hpos | hneg
    · exact ha (hpos.symm.trans hi)
    · exact ha (inv_eq_one.mp (hneg.symm.trans hi))
  obtain ⟨lam, hperm, hmixed, _hsign, hcentral, hcase⟩ :=
    ggTBJ_sp_blockData_rank_three hp hK4 hζ t ⟨0, htn 0⟩ hJ hcount
  have hshape : lam ≠ 1 ∧ ∀ i, t i = lam ∨ t i = lam⁻¹ := by
    rcases hcase with ⟨hlam, hzero⟩ | h
    · haveI : IsEmpty {i : Fin 3 // t i = 1} := ⟨fun i => htn i.1 i.2⟩
      simp at hzero
    · exact h
  have haLam : a = lam ∨ a = lam⁻¹ := by
    rcases hta (0 : Fin 3) with ha₀ | ha₀ <;> rcases hshape.2 (0 : Fin 3) with hl₀ | hl₀
    · exact Or.inl (ha₀.symm.trans hl₀)
    · exact Or.inr (ha₀.symm.trans hl₀)
    · exact Or.inr (by simpa only [inv_inv] using congrArg Inv.inv (ha₀.symm.trans hl₀))
    · exact Or.inl (by simpa only [inv_inv] using congrArg Inv.inv (ha₀.symm.trans hl₀))
  let q : MulAut (Fin 3 → Multiplicative (ZMod p)) :=
    diagAut ε (fun i => coord_sign_mul_self (hε i))
  let H := (ggAutomizer J (spTorusSp (m := 3) hζ).range).map
    (MulAut.congr κ.symm).toMonoidHom
  have hgen : ∀ i j : Fin 3, i ≠ j → ∀ f,
      ggTBJSpC_reflElt t i j * spTorusSp hζ (q f) * (ggTBJSpC_reflElt t i j)⁻¹ =
        spTorusSp hζ (q (permAut (Equiv.swap i j) f)) := by
    intro i j hij f
    have hcov : q * permAut (Equiv.swap i j) * q⁻¹ = ggTBJSpC_reflAut p 3 t i j :=
      ggTBJSpC_diagAut_conj_reflAut t a a⁻¹ ε hε hta htε hij
    have hcov' : q * permAut (Equiv.swap i j) = ggTBJSpC_reflAut p 3 t i j * q := by
      have h := congrArg (fun v : MulAut _ => v * q) hcov
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
    have hqrefl : q (permAut (Equiv.swap i j) f) = ggTBJSpC_reflAut p 3 t i j (q f) := by
      simpa only [MulAut.mul_apply] using congrArg (fun v : MulAut _ => v f) hcov'
    rw [hqrefl]
    by_cases h : t i = t j
    · exact ggTBJSpC_reflElt_conj_same hζ h (q f)
    · exact ggTBJSpC_reflElt_conj_mixed hζ h (q f)
  apply SpCoord.eq_closure_pair_of_fix_diagonal H
  · intro u hu
    exact ggTBJ_sp_torus_automizer_signed_of_coordinates hp hζo hζ J q
      (isSignedPerm_diagAut ε hε) κ hκ hu
  · intro u hu
    obtain ⟨n, hn, hact⟩ := (mem_map_congr_ggAutomizer_iff _ J κ u).mp hu
    let δ : Fin 3 → Multiplicative (ZMod p) := fun _ => ofAdd (1 : ZMod p)
    let β : Kˣ := zmodPowHom hζ (ofAdd (1 : ZMod p))
    have hpos : ∀ i, t i = a → zmodPowHom hζ (q δ i) = β := by
      intro i hi
      simp [q, diagAut_apply, (htε i).1 hi, δ, β]
    have hneg : ∀ i, t i = a⁻¹ → zmodPowHom hζ (q δ i) = β⁻¹ := by
      intro i hi
      have hqi : q δ i = (ofAdd (1 : ZMod p) : Multiplicative (ZMod p))⁻¹ := by
        simp only [q, diagAut_apply, (htε i).2 hi, δ, toAdd_ofAdd, mul_one]
        rfl
      rw [hqi, map_inv]
    have hcond : ∃ c : Kˣ, ∀ i,
        (t i = lam → zmodPowHom hζ (q δ i) = c) ∧
          (t i = lam⁻¹ → zmodPowHom hζ (q δ i) = c⁻¹) := by
      rcases haLam with hal | hal
      · refine ⟨β, fun i => ⟨fun hi => hpos i (hi.trans hal.symm),
          fun hi => hneg i (hi.trans (congrArg Inv.inv hal).symm)⟩⟩
      · have hainv : a⁻¹ = lam := by
          simpa only [inv_inv] using congrArg Inv.inv hal
        refine ⟨β⁻¹, fun i => ⟨fun hi => hneg i (hi.trans hainv.symm), fun hi => ?_⟩⟩
        rw [inv_inv]
        exact hpos i (hi.trans hal.symm)
    have hc := hcentral (fun i => zmodPowHom hζ (q δ i)) (Or.inr ⟨hshape.1, hcond⟩) n hn
    have hc' : spTorusSp hζ (q δ) * n = n * spTorusSp hζ (q δ) := by
      simpa only [ggTBJSpC_spTorusSp_eq_diagSp hζ (q δ)] using hc
    change u δ = δ
    apply κ.injective
    apply Subtype.ext
    have h := hact δ
    rw [hκ δ, hκ (u δ)] at h
    rw [hκ (u δ), hκ δ]
    calc spTorusSp hζ (q (u δ)) = n * spTorusSp hζ (q δ) * n⁻¹ := h.symm
      _ = spTorusSp hζ (q δ) := by rw [← hc']; group
  · refine (mem_map_congr_ggAutomizer_iff _ J κ (permAut (Equiv.swap (0 : Fin 3) 1))).mpr
      ⟨ggTBJSpC_reflElt t 0 1,
        ggTBJSpC_reflElt_mem_of_paired hshape.1 hperm hmixed (hshape.2 0) (hshape.2 1)
          (by decide), ?_⟩
    intro f
    rw [hκ f, hκ (permAut (Equiv.swap (0 : Fin 3) 1) f)]
    exact hgen 0 1 (by decide) f
  · refine (mem_map_congr_ggAutomizer_iff _ J κ (permAut (Equiv.swap (1 : Fin 3) 2))).mpr
      ⟨ggTBJSpC_reflElt t 1 2,
        ggTBJSpC_reflElt_mem_of_paired hshape.1 hperm hmixed (hshape.2 1) (hshape.2 2)
          (by decide), ?_⟩
    intro f
    rw [hκ f, hκ (permAut (Equiv.swap (1 : Fin 3) 2) f)]
    exact hgen 1 2 (by decide) f

theorem ggTBJ_sp_rank_three_automizer {p : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    (t : Fin 3 → Kˣ) (ht : ∃ i, t i ≠ 1)
    {J : Subgroup (CFSG.Assembly.LargeEvenSpGroup K 3)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({CFSG.SeitzReduction.SymplecticPilot.diagSp K 3 t} :
        Set (CFSG.Assembly.LargeEvenSpGroup K 3))))
    (hcount : p ^ 2 * Nat.card {f : Fin 3 → Multiplicative (ZMod p) //
      ∀ j ∈ J, spTorusSp hζ f * j = j * spTorusSp hζ f} ≤ p ^ 3) :
    ∃ (q : MulAut (Fin 3 → Multiplicative (ZMod p)))
      (κ : (Fin 3 → Multiplicative (ZMod p)) ≃* (spTorusSp (m := 3) hζ).range),
      IsSignedPerm q ∧
      (∀ f, (κ f : CFSG.Assembly.LargeEvenSpGroup K 3) = spTorusSp hζ (q f)) ∧
      ((ggAutomizer J (spTorusSp (m := 3) hζ).range).map (MulAut.congr κ.symm).toMonoidHom =
          Subgroup.closure ({sgnAut (2 : Fin 3), permAut (Equiv.swap (1 : Fin 3) 2)} :
            Set (MulAut (Fin 3 → Multiplicative (ZMod p)))) ∨
        (ggAutomizer J (spTorusSp (m := 3) hζ).range).map (MulAut.congr κ.symm).toMonoidHom =
          Subgroup.closure ({permAut (Equiv.swap (0 : Fin 3) 1),
            permAut (Equiv.swap (1 : Fin 3) 2)} :
            Set (MulAut (Fin 3 → Multiplicative (ZMod p))))) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let κ₀ := MonoidHom.ofInjective (spTorusSp_injective (m := 3) hζ hζo)
  obtain ⟨lam, _hperm, _hmixed, _hsign, _hcentral, hcase⟩ :=
    ggTBJ_sp_blockData_rank_three hp hK4 hζ t ht hJ hcount
  rcases hcase with ⟨hlam, hzero⟩ | ⟨hlam, hcover⟩
  · obtain ⟨a, ha⟩ := ht
    let I : Finset (Fin 3) := Finset.univ.filter fun i => t i = 1
    have hIcard : I.card = 2 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype, I] using hzero
    have hI : I = Finset.univ.erase a := by
      apply Finset.eq_of_subset_of_card_le
      · intro i hi
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ i⟩
        intro hia
        exact ha (hia ▸ (Finset.mem_filter.mp hi).2)
      · simp [hIcard]
    have hzero' : ∀ i, i ≠ a → t i = 1 := by
      intro i hi
      have hiI : i ∈ I := by rw [hI]; simp [hi]
      exact (Finset.mem_filter.mp hiI).2
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 a
    have hσ₀ : σ 0 = a := Equiv.swap_apply_left 0 a
    have hpos : ∀ i : Fin 3, i ≠ 0 → t (σ i) = 1 := by
      intro i hi
      exact hzero' (σ i) (fun h => hi (σ.injective (h.trans hσ₀.symm)))
    let q : MulAut (Fin 3 → Multiplicative (ZMod p)) := permAut σ
    let κ := q.trans κ₀
    have hκ : ∀ f, (κ f : CFSG.Assembly.LargeEvenSpGroup K 3) = spTorusSp hζ (q f) :=
      fun _ => rfl
    refine ⟨q, κ, ⟨σ, fun _ => 1, fun _ => Or.inl rfl,
      fun f i => by simp [q, permAut_apply]⟩, hκ, Or.inl ?_⟩
    exact ggTBJ_sp_zero_block_automizer hp hK4 hζo hζ t σ (hσ₀.symm ▸ ha)
      (hpos 1 (by decide)) (hpos 2 (by decide)) hJ hcount κ hκ
  · have hlamInv : lam ≠ lam⁻¹ := by
      intro h
      have hsq : lam * lam = 1 :=
        (congrArg (fun z : Kˣ => z * lam) h).trans (inv_mul_cancel lam)
      have hval : (lam : K) * (lam : K) = 1 := by
        simpa only [Units.val_mul, Units.val_one] using
          congrArg (fun z : Kˣ => (z : K)) hsq
      have hval' : (lam : K) = 1 := by
        rcases mul_self_eq_one_iff.mp hval with h | h
        · exact h
        · simpa only [CharTwo.neg_eq] using h
      exact hlam (Units.ext hval')
    let ε : Fin 3 → ZMod p := fun i => if t i = lam then 1 else -1
    have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
      intro i
      dsimp [ε]
      split <;> simp
    have htε : ∀ i, (t i = lam → ε i = 1) ∧ (t i = lam⁻¹ → ε i = -1) := by
      intro i
      constructor
      · intro hi
        simp [ε, hi]
      · intro hi
        have hi' : t i ≠ lam := fun h => hlamInv (h.symm.trans hi)
        simp [ε, hi']
    let q : MulAut (Fin 3 → Multiplicative (ZMod p)) :=
      diagAut ε (fun i => coord_sign_mul_self (hε i))
    let κ := q.trans κ₀
    have hκ : ∀ f, (κ f : CFSG.Assembly.LargeEvenSpGroup K 3) = spTorusSp hζ (q f) :=
      fun _ => rfl
    refine ⟨q, κ, isSignedPerm_diagAut ε hε, hκ, Or.inr ?_⟩
    exact ggTBJ_sp_paired_block_automizer hp hK4 hζo hζ t lam hlam hcover
      ε hε htε hJ hcount κ hκ

end CFSG.StandardType
