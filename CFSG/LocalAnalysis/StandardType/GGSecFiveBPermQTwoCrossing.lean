module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoKBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermQTwoCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotGlobalNormalModel
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourNormal

public section

namespace CFSG.StandardType

open Polynomial Matrix CFSG.RankThree.CALinearPlane
open scoped MatrixGroups

namespace QTwoBlocks

theorem card_fixS_compl {m e s d : ℕ} (ε : Fin m ≃ (Fin e × Fin s) ⊕ Fin d)
    (S : Finset (Fin s)) : (SLNS.fixS ε Sᶜ).card = e * S.card + d := by
  classical
  have h := Finset.card_equiv ε
    (s := SLNS.fixS ε Sᶜ)
    (t := ((Finset.univ : Finset (Fin e)).product S).disjSum
      (Finset.univ : Finset (Fin d))) (fun x => by
        rcases hε : ε x with ⟨a, i⟩ | j <;> simp [SLNS.mem_fixS, SLNS.inT, hε])
  simpa only [Finset.card_disjSum, Finset.product_eq_sprod, Finset.card_product, Finset.card_univ,
    Fintype.card_fin] using h

private theorem disjoint_fixS_compl {m e s d : ℕ}
    (ε : Fin m ≃ (Fin e × Fin s) ⊕ Fin d) (hd : d = 0)
    {S T : Finset (Fin s)} (hST : Disjoint S T) :
    Disjoint (SLNS.fixS ε Sᶜ) (SLNS.fixS ε Tᶜ) := by
  classical
  refine Finset.disjoint_left.mpr fun x hxS hxT => ?_
  rcases hε : ε x with ⟨a, i⟩ | j
  · have hiS : i ∈ S := by simpa [SLNS.mem_fixS, SLNS.inT, hε] using hxS
    have hiT : i ∈ T := by simpa [SLNS.mem_fixS, SLNS.inT, hε] using hxT
    exact Finset.disjoint_left.mp hST hiS hiT
  · have hj := j.isLt
    omega

private theorem disjoint_sdiff_fixS_compl {m e s d : ℕ}
    (ε : Fin m ≃ (Fin e × Fin s) ⊕ Fin d)
    {S T : Finset (Fin s)} (R : Finset (Fin s)) (hST : Disjoint S T) :
    Disjoint (SLNS.fixS ε Sᶜ \ SLNS.fixS ε Rᶜ) (SLNS.fixS ε Tᶜ) := by
  classical
  refine Finset.disjoint_left.mpr fun x hx hxT => ?_
  obtain ⟨hxS, hxR⟩ := Finset.mem_sdiff.mp hx
  rcases hε : ε x with ⟨a, i⟩ | j
  · have hiS : i ∈ S := by simpa [SLNS.mem_fixS, SLNS.inT, hε] using hxS
    have hiT : i ∈ T := by simpa [SLNS.mem_fixS, SLNS.inT, hε] using hxT
    exact Finset.disjoint_left.mp hST hiS hiT
  · simp [SLNS.mem_fixS, SLNS.inT, hε] at hxR

private theorem commute_coordBlockSL_map {G : Type} [Group G] {F : Type} [Field F]
    {m : ℕ} (κ : SL(m, F) →* G) {I J : Finset (Fin m)} (hIJ : Disjoint I J) :
    ∀ x ∈ (coordBlockSL F I).map κ, ∀ z ∈ (coordBlockSL F J).map κ, x * z = z * x := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  have hu' : u ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear I := by
    rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    simpa only [Matrix.one_apply] using mem_coordBlockSL_iff.mp hu
  have hv' : v ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear J := by
    rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    simpa only [Matrix.one_apply] using mem_coordBlockSL_iff.mp hv
  have huv := CFSG.SeitzReduction.LinearPilot.commute_blockSpecialLinear_of_disjoint hIJ hu' hv'
  simpa only [map_mul] using congrArg κ huv.eq

end QTwoBlocks

namespace GGSecFiveBPermQTwoKFrame

variable {G : Type} [Group G] {Bs K : Subgroup G} {n r m d : ℕ}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {π : Fin (r + 2) ≃ Fin n}
  {g : (ZMod 2)[X]} [Fact (Irreducible g)]
  {ε : Fin m ≃ (Fin (CoordSL.rootPB g).dim × Fin (r + 1)) ⊕ Fin d}
  {hC : (CoordSL.rootMat g).det = 1} {hCp : CoordSL.rootMat g ^ 3 = 1} {κ : SL(m, ZMod 2) →* G}

private theorem crossing_even_indices [Finite G]
    (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2)
    (hlift : ∀ a b : Fin n, a ≠ b → ∃ w, ∃ hw : w ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap a b))
    (hd : d = 0) {i j k l : Fin (r + 1)}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ∀ x ∈ ggBlockComm Bs eta {π i.succ, π j.succ},
      ∀ z ∈ ggBlockComm Bs eta {π l.succ, π 0}, x * z = z * x := by
  classical
  have hS : ({i, j} : Finset (Fin (r + 1))) ≠ Finset.univ := by
    intro h
    have hk : k ∈ ({i, j} : Finset (Fin (r + 1))) := h.symm ▸ Finset.mem_univ k
    simp [hik.symm, hjk.symm] at hk
  have hT : ({l, k} : Finset (Fin (r + 1))) ≠ Finset.univ := by
    intro h
    have hi : i ∈ ({l, k} : Finset (Fin (r + 1))) := h.symm ▸ Finset.mem_univ i
    simp [hil, hik] at hi
  have hpair : ggBlockComm Bs eta {π i.succ, π j.succ} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({i, j} : Finset _)ᶜ)).map κ := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
      Set.image_singleton] using hF.blockComm hBs hyB hK (S := {i, j})
        (Finset.insert_nonempty _ _) hS (by
          rw [QTwoBlocks.card_fixS_compl, hdim, hd]
          simp [hij])
  have hother : ggBlockComm Bs eta {π l.succ, π k.succ} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({l, k} : Finset _)ᶜ)).map κ := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
      Set.image_singleton] using hF.blockComm hBs hyB hK (S := {l, k})
        (Finset.insert_nonempty _ _) hT
        (by
          rw [QTwoBlocks.card_fixS_compl, hdim, hd]
          simp [hkl.symm])
  have hST : Disjoint ({i, j} : Finset _) {l, k} := by
    refine Finset.disjoint_left.mpr fun a haS haT => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at haS haT
    rcases haS with rfl | rfl
    · exact (not_or.mpr ⟨hil, hik⟩) haT
    · exact (not_or.mpr ⟨hjl, hjk⟩) haT
  obtain ⟨w, hw, hτ⟩ := hlift (π 0) (π k.succ)
    (π.injective.ne (Fin.succ_ne_zero k).symm)
  let f := (MulAut.conj w).toMonoidHom
  have hfix (a : Fin (r + 1)) (hak : a ≠ k) :
      Equiv.swap (π 0) (π k.succ) (π a.succ) = π a.succ := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact π.injective.ne (Fin.succ_ne_zero a)
    · intro h
      exact hak (Fin.succ_injective (r + 1) (π.injective h))
  have hX : (ggBlockComm Bs eta {π i.succ, π j.succ}).map f =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({i, j} : Finset _)ᶜ)).map κ := by
    rw [ggBlockComm_map_conj hw hτ]
    simpa only [Set.image_insert_eq, Set.image_singleton, hfix i hik, hfix j hjk] using hpair
  have hZ : (ggBlockComm Bs eta {π l.succ, π 0}).map f =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({l, k} : Finset _)ᶜ)).map κ := by
    rw [ggBlockComm_map_conj hw hτ]
    simpa only [Set.image_insert_eq, Set.image_singleton, hfix l hkl.symm,
      Equiv.swap_apply_left] using hother
  intro x hx z hz
  have hfx := hX ▸ Subgroup.mem_map_of_mem f hx
  have hfz := hZ ▸ Subgroup.mem_map_of_mem f hz
  apply (MulAut.conj w).injective
  change f (x * z) = f (z * x)
  simpa only [map_mul] using QTwoBlocks.commute_coordBlockSL_map κ
    (QTwoBlocks.disjoint_fixS_compl ε hd hST) (f x) hfx (f z) hfz

private theorem crossing_odd_indices [Finite G]
    (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2)
    (hlift : ∀ a b : Fin n, a ≠ b → ∃ w, ∃ hw : w ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap a b))
    (hd : d = 1) {i j k l : Fin (r + 1)}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ∀ x ∈ ggBlockComm Bs eta {π i.succ, π j.succ} ⊓
        Subgroup.centralizer (ggBlockComm Bs eta {π k.succ} : Set G),
      ∀ z ∈ ggBlockComm Bs eta {π 0}, x * z = z * x := by
  classical
  have hS : ({i, j} : Finset (Fin (r + 1))) ≠ Finset.univ := by
    intro h
    have hk : k ∈ ({i, j} : Finset (Fin (r + 1))) := h.symm ▸ Finset.mem_univ k
    simp [hik.symm, hjk.symm] at hk
  have hR : ({k} : Finset (Fin (r + 1))) ≠ Finset.univ := by
    intro h
    have hi : i ∈ ({k} : Finset (Fin (r + 1))) := h.symm ▸ Finset.mem_univ i
    simp [hik] at hi
  have hT : ({l} : Finset (Fin (r + 1))) ≠ Finset.univ := by
    intro h
    have hi : i ∈ ({l} : Finset (Fin (r + 1))) := h.symm ▸ Finset.mem_univ i
    simp [hil] at hi
  have hpair : ggBlockComm Bs eta {π i.succ, π j.succ} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({i, j} : Finset _)ᶜ)).map κ := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq,
      Set.image_singleton] using hF.blockComm hBs hyB hK (S := {i, j})
        (Finset.insert_nonempty _ _) hS (by
          rw [QTwoBlocks.card_fixS_compl, hdim, hd]
          simp [hij])
  have hcentral : ggBlockComm Bs eta {π k.succ} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({k} : Finset _)ᶜ)).map κ := by
    simpa only [Finset.coe_singleton, Set.image_singleton] using hF.blockComm hBs hyB hK
      (S := {k}) (Finset.singleton_nonempty _) hR
      (by rw [QTwoBlocks.card_fixS_compl, hdim, hd]; simp)
  have hother : ggBlockComm Bs eta {π l.succ} =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({l} : Finset _)ᶜ)).map κ := by
    simpa only [Finset.coe_singleton, Set.image_singleton] using hF.blockComm hBs hyB hK
      (S := {l}) (Finset.singleton_nonempty _) hT
      (by rw [QTwoBlocks.card_fixS_compl, hdim, hd]; simp)
  have hJI : ∃ a ∈ SLNS.fixS ε ({k} : Finset _)ᶜ,
      a ∉ SLNS.fixS ε ({i, j} : Finset _)ᶜ := by
    let a : Fin (CoordSL.rootPB g).dim := ⟨0, by omega⟩
    refine ⟨ε.symm (Sum.inl (a, k)), ?_, ?_⟩
    · simp [SLNS.mem_fixS, SLNS.inT]
    · simp [SLNS.mem_fixS, SLNS.inT, hik.symm, hjk.symm]
  have hST : Disjoint ({i, j} : Finset _) {l} := by
    refine Finset.disjoint_left.mpr fun a haS haT => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at haS haT
    subst a
    exact (not_or.mpr ⟨hil.symm, hjl.symm⟩) haS
  obtain ⟨w, hw, hτ⟩ := hlift (π 0) (π l.succ)
    (π.injective.ne (Fin.succ_ne_zero l).symm)
  let f := (MulAut.conj w).toMonoidHom
  have hfix (a : Fin (r + 1)) (hal : a ≠ l) :
      Equiv.swap (π 0) (π l.succ) (π a.succ) = π a.succ := by
    apply Equiv.swap_apply_of_ne_of_ne
    · exact π.injective.ne (Fin.succ_ne_zero a)
    · intro h
      exact hal (Fin.succ_injective (r + 1) (π.injective h))
  have hX : (ggBlockComm Bs eta {π i.succ, π j.succ}).map f =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({i, j} : Finset _)ᶜ)).map κ := by
    rw [ggBlockComm_map_conj hw hτ]
    simpa only [Set.image_insert_eq, Set.image_singleton, hfix i hil, hfix j hjl] using hpair
  have hRmap : (ggBlockComm Bs eta {π k.succ}).map f =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({k} : Finset _)ᶜ)).map κ := by
    rw [ggBlockComm_map_conj hw hτ]
    simpa only [Set.image_singleton, hfix k hkl] using hcentral
  have hZ : (ggBlockComm Bs eta {π 0}).map f =
      (coordBlockSL (ZMod 2) (SLNS.fixS ε ({l} : Finset _)ᶜ)).map κ := by
    rw [ggBlockComm_map_conj hw hτ]
    simpa only [Set.image_singleton, Equiv.swap_apply_left] using hother
  intro x hx z hz
  have hfx : f x ∈ (coordBlockSL (ZMod 2) (SLNS.fixS ε ({i, j} : Finset _)ᶜ)).map κ ⊓
      Subgroup.centralizer
        ((coordBlockSL (ZMod 2) (SLNS.fixS ε ({k} : Finset _)ᶜ)).map κ : Set G) := by
    refine ⟨hX ▸ Subgroup.mem_map_of_mem f hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    rw [← hRmap] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp hx.2 u hu)
  rw [coordBlockSL_map_inf_centralizer_eq_sdiff κ hF.1 _ _
    (by rw [QTwoBlocks.card_fixS_compl, hdim, hd]; simp) hJI] at hfx
  have hfz := hZ ▸ Subgroup.mem_map_of_mem f hz
  apply (MulAut.conj w).injective
  change f (x * z) = f (z * x)
  simpa only [map_mul] using QTwoBlocks.commute_coordBlockSL_map κ
    (QTwoBlocks.disjoint_sdiff_fixS_compl ε {k} hST) (f x) hfx (f z) hfz

theorem crossing_even [Finite G]
    (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2) (hr : 3 ≤ r)
    (hlift : ∀ a b : Fin n, a ≠ b → ∃ w, ∃ hw : w ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap a b))
    (hd : d = 0) :
    ∀ x ∈ ggBlockComm Bs eta {π 1, π 2},
      ∀ z ∈ ggBlockComm Bs eta {π (Fin.last (r + 1)), π 0}, x * z = z * x := by
  let i : Fin (r + 1) := ⟨0, by omega⟩
  let j : Fin (r + 1) := ⟨1, by omega⟩
  let k : Fin (r + 1) := ⟨2, by omega⟩
  have h := crossing_even_indices hF hBs hyB hK hdim hlift hd
    (i := i) (j := j) (k := k) (l := Fin.last r)
    (by simp [i, j, Fin.ext_iff]) (by simp [i, k, Fin.ext_iff])
    (by intro h; have hv := congrArg Fin.val h; change 0 = r at hv; omega)
    (by simp [j, k, Fin.ext_iff])
    (by intro h; have hv := congrArg Fin.val h; change 1 = r at hv; omega)
    (by intro h; have hv := congrArg Fin.val h; change 2 = r at hv; omega)
  have hi : i.succ = (1 : Fin (r + 2)) := by
    apply Fin.ext
    change 1 = 1 % (r + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hj : j.succ = (2 : Fin (r + 2)) := by
    apply Fin.ext
    change 2 = 2 % (r + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hl : (Fin.last r).succ = Fin.last (r + 1) := rfl
  simpa only [hi, hj, hl] using h

theorem crossing_odd [Finite G]
    (hF : GGSecFiveBPermQTwoKFrame Bs K eta π ε hC hCp κ)
    (hBs : ∀ x ∈ Subgroup.centralizer (Bs : Set G), x ^ 3 = 1 → x ∈ Bs)
    {y : G} (hyB : y ∈ Bs)
    (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    (hdim : (CoordSL.rootPB g).dim = 2) (hr : 3 ≤ r)
    (hlift : ∀ a b : Fin n, a ≠ b → ∃ w, ∃ hw : w ∈ Subgroup.normalizer (Bs : Set G),
      MulAut.congr eta (ggConjAut Bs hw) = SpCoord.permAut (Equiv.swap a b))
    (hd : d = 1) :
    ∀ x ∈ ggBlockComm Bs eta {π 1, π 2} ⊓
        Subgroup.centralizer (ggBlockComm Bs eta {π 3} : Set G),
      ∀ z ∈ ggBlockComm Bs eta {π 0}, x * z = z * x := by
  let i : Fin (r + 1) := ⟨0, by omega⟩
  let j : Fin (r + 1) := ⟨1, by omega⟩
  let k : Fin (r + 1) := ⟨2, by omega⟩
  let l : Fin (r + 1) := ⟨3, by omega⟩
  have h := crossing_odd_indices hF hBs hyB hK hdim hlift hd
    (i := i) (j := j) (k := k) (l := l)
    (by simp [i, j, Fin.ext_iff]) (by simp [i, k, Fin.ext_iff])
    (by simp [i, l, Fin.ext_iff]) (by simp [j, k, Fin.ext_iff])
    (by simp [j, l, Fin.ext_iff]) (by simp [k, l, Fin.ext_iff])
  have hi : i.succ = (1 : Fin (r + 2)) := by
    apply Fin.ext
    change 1 = 1 % (r + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hj : j.succ = (2 : Fin (r + 2)) := by
    apply Fin.ext
    change 2 = 2 % (r + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hk : k.succ = (3 : Fin (r + 2)) := by
    apply Fin.ext
    change 3 = 3 % (r + 2)
    rw [Nat.mod_eq_of_lt (by omega)]
  simpa only [hi, hj, hk] using h

end GGSecFiveBPermQTwoKFrame

end CFSG.StandardType

end
