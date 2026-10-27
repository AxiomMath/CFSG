module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat
public import CFSG.Monster.B.TwoA.Sp8.GenActionHom

public section

open scoped Pointwise

attribute [local instance] commutatorElement

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

private theorem lup8u2b_charP_two (hK : Nat.card K = 4) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨s, hs, m, hsp, hm⟩ := FiniteField.card' (K := K)
  have hm2 : s ^ (m : ℕ) = 2 ^ 2 := by
    rw [← hm, ← Nat.card_eq_fintype_card, hK]
    norm_num
  have h1 : s ∣ 2 ^ 2 := by
    rw [← hm2]
    exact dvd_pow_self s m.ne_zero
  have h2 : s ∣ 2 := hsp.dvd_of_dvd_pow h1
  have hs2 : s = 2 := (Nat.prime_dvd_prime_iff_eq hsp Nat.prime_two).mp h2
  rwa [hs2] at hs

private theorem lup8u2b_witData {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ} {K : Type} [Field K]
    [Finite K] (M : lup8f_UnitaryMarking Bs L n K)
    (b : ↥(lup8f_E' L Bs)) :
    ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K 2))
        (LargeEvenGUSet (Fin n) K 2),
      LargeEvenInduces M.theta
        (fun l l' : ↥L => (l' : G) =
          (((b : lup8f_HT L Bs) : G)⁻¹)⁻¹ * (l : G) * (((b : lup8f_HT L Bs) : G)⁻¹)) φ :=
  M.action (((b : lup8f_HT L Bs) : G))⁻¹
    (Bs.inv_mem (Subgroup.mem_subgroupOf.mp b.2))

private noncomputable def lup8u2b_wit (M : lup8f_UnitaryMarking Bs L n K)
    (b : ↥(lup8f_E' L Bs)) : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin n) K 2)) :=
  (lup8u2b_witData M b).choose

private noncomputable def lup8u2b_mat (M : lup8f_UnitaryMarking Bs L n K)
    (b : ↥(lup8f_E' L Bs)) : GL (Fin n) K :=
  ((lup8u2b_witData M b).choose_spec.1).choose

private lemma lup8u2b_mat_mem {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ} {K : Type} [Field K]
    [Finite K] (M : lup8f_UnitaryMarking Bs L n K)
    (b : ↥(lup8f_E' L Bs)) :
    lup8u2b_mat M b ∈ LargeEvenGUSet (Fin n) K 2 :=
  ((lup8u2b_witData M b).choose_spec.1).choose_spec.1

private lemma lup8u2b_mat_graphAut {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ} {K : Type} [Field K]
    [Finite K] (M : lup8f_UnitaryMarking Bs L n K)
    (b : ↥(lup8f_E' L Bs)) :
    LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K 2))
      (fun h h' => (h' : GL (Fin n) K) =
        lup8u2b_mat M b * (h : GL (Fin n) K) * (lup8u2b_mat M b)⁻¹)
      (lup8u2b_wit M b) :=
  ((lup8u2b_witData M b).choose_spec.1).choose_spec.2

private lemma lup8u2b_mat_induces {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ} {K : Type} [Field K]
    [Finite K] (M : lup8f_UnitaryMarking Bs L n K)
    (b : ↥(lup8f_E' L Bs)) :
    LargeEvenInduces M.theta
      (fun l l' : ↥L => (l' : G) =
        (((b : lup8f_HT L Bs) : G)⁻¹)⁻¹ * (l : G) * (((b : lup8f_HT L Bs) : G)⁻¹))
      (lup8u2b_wit M b) :=
  (lup8u2b_witData M b).choose_spec.2

private lemma lup8u2b_conjLQ_apply {H : Type} [Group H] {N : Subgroup H} [N.Normal]
    {L' E' : Subgroup H} (h : E' ≤ Subgroup.normalizer (L' : Set H)) (b : ↥E') (l : ↥L') :
    (lup8f_conjLQ N L' E' h b l : H ⧸ N) =
      QuotientGroup.mk' N ((b : H) * (l : H) * (b : H)⁻¹) := rfl

noncomputable def lup8f_frame0_of_eps (hperf : commutator ↥L = ⊤)
    (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (eps : ↥((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) ≃* ↥(LargeEvenSUGroup (Fin n) K 2))
    (heps : lup8f_EpsOver M C.N eps) :
    lup8f_UFrame0 (lup8f_HT L Bs) C.N (lup8f_L' L Bs) (lup8f_E' L Bs) n K := by
  classical
  haveI hchar : CharP K 2 := lup8u2b_charP_two M.card_K
  let H := lup8f_HT L Bs
  let L' : Subgroup H := lup8f_L' L Bs
  let E' : Subgroup H := lup8f_E' L Bs
  let N : Subgroup H := C.N
  haveI : N.Normal := C.normal
  let SU := LargeEvenSUGroup (Fin n) K 2
  have hperfL' : commutator ↥L' = ⊤ := by
    let e : ↥(L.subgroupOf (L ⊔ Bs)) ≃* ↥L := Subgroup.subgroupOfEquivOfLe le_sup_left
    have h := Subgroup.map_commutator (⊤ : Subgroup ↥L) (⊤ : Subgroup ↥L) e.symm.toMonoidHom
    rw [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at h
    rw [show (⁅(⊤ : Subgroup ↥L), ⊤⁆ : Subgroup ↥L) = commutator ↥L from
          (commutator_def _).symm,
        show (⁅(⊤ : Subgroup ↥L'), ⊤⁆ : Subgroup ↥L') = commutator ↥L' from
          (commutator_def _).symm,
        hperf] at h
    rw [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at h
    exact h.symm
  refine
    { le_L := C.le_L
      central := C.central
      E'_le_norm := C.E'_le_norm
      eps := eps
      mat := lup8u2b_mat M
      mat_mem := fun b => lup8u2b_mat_mem M b
      mat_ind := ?_ }
  intro b l
  let bG : G := (b : H)
  have hb : bG ∈ Bs := Subgroup.mem_subgroupOf.mp b.2
  let A : GL (Fin n) K := lup8u2b_mat M b
  let φ : MulAut (LargeEvenProj SU) := lup8u2b_wit M b
  let mkL0 : ↥L' →* ↥(L'.map (QuotientGroup.mk' N)) :=
    { toFun := fun l => ⟨QuotientGroup.mk' N (l : H), Subgroup.mem_map_of_mem _ l.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp }
  let conjHom : ↥L' →* ↥(L'.map (QuotientGroup.mk' N)) :=
    { toFun := fun l => lup8f_conjLQ N L' E' C.E'_le_norm b l
      map_one' := by
        apply Subtype.ext
        rw [lup8u2b_conjLQ_apply]
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        rw [Subgroup.coe_mul]
        rw [lup8u2b_conjLQ_apply, lup8u2b_conjLQ_apply, lup8u2b_conjLQ_apply]
        simp only [map_mul, map_inv, Subgroup.coe_mul]
        group }
  let q1 : ↥L' →* ↥SU := eps.toMonoidHom.comp conjHom
  let ψ : ↥L' →* GL (Fin n) K :=
    ((MulAut.conj A).toMonoidHom.comp SU.subtype).comp (eps.toMonoidHom.comp mkL0)
  have hSU : ∀ l : ↥L', ψ l ∈ SU := fun l => by
    have hconj : ψ l = A * (eps (mkL0 l) : GL (Fin n) K) * A⁻¹ :=
      MulAut.conj_apply A ((eps (mkL0 l)) : GL (Fin n) K)
    rw [hconj]
    exact CFSG.LocalAnalysis.GLTheoremA.T156.Uni.conj_mem_su (j := 1)
      (lup8u2b_mat_mem M b) (eps (mkL0 l)).2
  let q2 : ↥L' →* ↥SU :=
    { toFun := fun l => ⟨ψ l, hSU l⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun x y => Subtype.ext (map_mul ψ x y) }
  have hproj : ∀ l : ↥L', LargeEvenProjMk SU (q1 l) = LargeEvenProjMk SU (q2 l) := fun l => by
    let lG : ↥L := ⟨(l : G), Subgroup.mem_subgroupOf.mp l.2⟩
    have hbL : bG * (l : G) * bG⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (M.normalizes hb) (l : G)).mp
        (Subgroup.mem_subgroupOf.mp l.2)
    let l'L' : ↥L' := ⟨⟨bG * (l : G) * bG⁻¹, Subgroup.mem_sup_left hbL⟩, hbL⟩
    let l'G : ↥L := ⟨(l'L' : G), Subgroup.mem_subgroupOf.mp l'L'.2⟩
    have hrel : (l'G : G) = (bG⁻¹)⁻¹ * (lG : G) * (bG⁻¹) := by
      show bG * (l : G) * bG⁻¹ = (bG⁻¹)⁻¹ * (l : G) * (bG⁻¹)
      rw [inv_inv]
    have hq2 : (q2 l : GL (Fin n) K) = A * (eps (mkL0 l) : GL (Fin n) K) * A⁻¹ :=
      MulAut.conj_apply A ((eps (mkL0 l)) : GL (Fin n) K)
    have hgraph := lup8u2b_mat_graphAut M b (eps (mkL0 l)) (q2 l) hq2
    have h1 : LargeEvenProjMk SU (eps (mkL0 l)) = M.theta (QuotientGroup.mk lG) := heps l
    have h2 : φ (M.theta (QuotientGroup.mk lG)) = M.theta (QuotientGroup.mk l'G) :=
      lup8u2b_mat_induces M b lG l'G hrel
    have h4 : mkL0 l'L' = conjHom l := by
      apply Subtype.ext
      change QuotientGroup.mk' N (l'L' : H) =
        (lup8f_conjLQ N L' E' C.E'_le_norm b l : H ⧸ N)
      rw [lup8u2b_conjLQ_apply]
      apply congrArg (QuotientGroup.mk' N)
      apply Subtype.ext
      rfl
    calc LargeEvenProjMk SU (q1 l)
        = LargeEvenProjMk SU (eps (conjHom l)) := rfl
      _ = LargeEvenProjMk SU (eps (mkL0 l'L')) := by rw [← h4]
      _ = M.theta (QuotientGroup.mk l'G) := heps l'L'
      _ = φ (M.theta (QuotientGroup.mk lG)) := h2.symm
      _ = φ (LargeEvenProjMk SU (eps (mkL0 l))) := by rw [← h1]
      _ = LargeEvenProjMk SU (q2 l) := hgraph
  have hz : ∀ l : ↥L', q1 l * (q2 l)⁻¹ ∈ Subgroup.center ↥SU := fun l => by
    have hker : (LargeEvenProjMk SU).ker ≤ Subgroup.center ↥SU := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center SU
    refine hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, hproj l, mul_inv_cancel]
  let Φ : ↥L' →* ↥SU :=
    { toFun := fun l => q1 l * (q2 l)⁻¹
      map_one' := by
        change q1 1 * (q2 1)⁻¹ = 1
        rw [map_one q1, map_one q2, inv_one, mul_one]
      map_mul' := fun x y => by
        have hzy : q1 y * (q2 y)⁻¹ ∈ Subgroup.center ↥SU := hz y
        rw [Subgroup.mem_center_iff] at hzy
        change q1 (x * y) * (q2 (x * y))⁻¹ =
          (q1 x * (q2 x)⁻¹) * (q1 y * (q2 y)⁻¹)
        rw [map_mul q1, map_mul q2, mul_inv_rev]
        calc q1 x * q1 y * ((q2 y)⁻¹ * (q2 x)⁻¹)
            = q1 x * ((q1 y * (q2 y)⁻¹) * (q2 x)⁻¹) := by group
          _ = q1 x * ((q2 x)⁻¹ * (q1 y * (q2 y)⁻¹)) := by rw [← hzy (q2 x)⁻¹]
          _ = q1 x * (q2 x)⁻¹ * (q1 y * (q2 y)⁻¹) := by group }
  have hle : commutator ↥L' ≤ Φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker]
    have hx : Φ x ∈ Subgroup.center ↥SU := hz x
    have hy : Φ y ∈ Subgroup.center ↥SU := hz y
    rw [Subgroup.mem_center_iff] at hx hy
    rw [show Φ ⁅x, y⁆ = ⁅Φ x, Φ y⁆ from map_commutatorElement Φ x y]
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (hx (Φ y)).symm
  have hΦ1 : Φ = 1 := by
    rw [← MonoidHom.ker_eq_top_iff]
    rw [eq_top_iff, ← hperfL']
    exact hle
  change (q1 l : GL (Fin n) K) = MulAut.conj A (eps (mkL0 l) : GL (Fin n) K)
  have h1 : Φ l = 1 := DFunLike.congr_fun hΦ1 l
  have h2 : (q1 l : GL (Fin n) K) * (q2 l : GL (Fin n) K)⁻¹ = 1 := by
    have := congrArg (fun x : ↥SU => (x : GL (Fin n) K)) h1
    simpa [Φ] using this
  have h3 : (q1 l : GL (Fin n) K) = (q2 l : GL (Fin n) K) := by
    rwa [mul_inv_eq_one] at h2
  rw [h3, MulAut.conj_apply]
  exact MulAut.conj_apply A ((eps (mkL0 l)) : GL (Fin n) K)

end CFSG.StandardType.GGXInL

end
