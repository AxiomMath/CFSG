module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.ComponentNormal
public import CFSG.Walter.Bender1970.S2.Subnormal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.Walter.Bender1970.S2.TwoSubgroup
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate43

public section

namespace CFSG.StandardType.ClassicalPosition.Block

open CFSG.Assembly

private lemma cc_hpair {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ x ∈ Units.val '' S, ∀ y ∈ Units.val '' S, x * y = y * x := by
  intro x hx y hy
  rcases hx with ⟨s, hs, rfl⟩
  rcases hy with ⟨s', hs', rfl⟩
  simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F))
    (hS s hs s' hs')

private lemma cc_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      a * b = b * a := by
  intro a ha b hb
  exact Algebra.adjoin_induction₂ (R := F) (A := Matrix ι ι F) (s := Units.val '' S)
    (p := fun a b _ _ => a * b = b * a)
    (fun x y hx hy => cc_hpair S hS x hx y hy)
    (fun r₁ r₂ => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, mul_comm])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun x y z hx hy hz hxz hyz => by rw [add_mul, mul_add, hxz, hyz])
    (fun x y z hx hy hz hxy hxz => by rw [mul_add, add_mul, hxy, hxz])
    (fun x y z hx hy hz hxz hyz => by
      rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc])
    (fun x y z hx hy hz hxy hxz => by
      rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc]) (x := a) (y := b) ha hb

private lemma cc_adjoin_commute_S {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (a : Matrix ι ι F) (ha : a ∈ Algebra.adjoin F (Units.val '' S))
    (s : GL ι F) (hs : s ∈ S) :
    a * (s : Matrix ι ι F) = (s : Matrix ι ι F) * a :=
  cc_adjoin_comm S hS a ha (s : Matrix ι ι F)
    (Algebra.subset_adjoin ⟨s, hs, rfl⟩)

private lemma cc_mem_adjoin_commute {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι]
    [Field F] (j : U →* GL ι F) (S : Set (GL ι F))
    (x : U) (hx : x ∈ (Subgroup.centralizer S).comap j) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (j x : Matrix ι ι F) * a = a * (j x : Matrix ι ι F) := by
  have hgen : Units.val '' S ⊆ Subalgebra.centralizer F {(j x : Matrix ι ι F)} := by
    intro y hy
    change y ∈ Subalgebra.centralizer F {(j x : Matrix ι ι F)}
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rcases hy with ⟨t, ht, rfl⟩
    have hmem := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx)) t ht
    have hm : (t : Matrix ι ι F) * (j x : Matrix ι ι F) =
        (j x : Matrix ι ι F) * (t : Matrix ι ι F) := by
      simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hmem
    exact hm.symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤ Subalgebra.centralizer F {(j x : Matrix ι ι F)} :=
    Algebra.adjoin_le hgen
  intro a ha
  exact (Subalgebra.mem_centralizer_iff F).mp (hA ha) (j x) (Set.mem_singleton _)

private lemma cc_inv_comm {R : Type} [Ring R] {x xi e : R} (hx : x * xi = 1)
    (hxi : xi * x = 1) (hc : x * e = e * x) : xi * e = e * xi := by
  calc xi * e = xi * e * (x * xi) := by rw [hx, mul_one]
    _ = xi * (e * x) * xi := by noncomm_ring
    _ = xi * (x * e) * xi := by rw [hc]
    _ = xi * x * e * xi := by noncomm_ring
    _ = e * xi := by rw [hxi]; noncomm_ring

private lemma cc_blk_mul_inv {R : Type} [Ring R] (x xi e : R) (hx : x * xi = 1)
    (hid : e * e = e) (hci : xi * e = e * xi) :
    (x * e + (1 - e)) * (xi * e + (1 - e)) = 1 := by
  have hxe : x * (xi * e) = e := by rw [← mul_assoc, hx, one_mul]
  have hexi : e * (xi * e) = xi * e := by
    calc e * (xi * e) = (e * xi) * e := by rw [mul_assoc]
      _ = (xi * e) * e := by rw [← hci]
      _ = xi * (e * e) := by rw [mul_assoc]
      _ = xi * e := by rw [hid]
  have hxe' : (x * e) * (xi * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private lemma cc_blk_inv_mul {R : Type} [Ring R] (x xi e : R) (hxi : xi * x = 1)
    (hid : e * e = e) (hc : x * e = e * x) :
    (xi * e + (1 - e)) * (x * e + (1 - e)) = 1 := by
  have hxe : xi * (x * e) = e := by rw [← mul_assoc, hxi, one_mul]
  have hexi : e * (x * e) = x * e := by
    calc e * (x * e) = (e * x) * e := by rw [mul_assoc]
      _ = (x * e) * e := by rw [← hc]
      _ = x * (e * e) := by rw [mul_assoc]
      _ = x * e := by rw [hid]
  have hxe' : (xi * e) * (x * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private def cc_blkAux {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) : GL ι F :=
  Units.mk ((x : Matrix ι ι F) * e + (1 - e))
    (((x⁻¹ : GL ι F) : Matrix ι ι F) * e + (1 - e))
    (cc_blk_mul_inv (x : Matrix ι ι F) ((x⁻¹ : GL ι F) : Matrix ι ι F) e
      (Units.mul_inv x) hid.eq
      (cc_inv_comm (Units.mul_inv x) (Units.inv_mul x) hcomm))
    (cc_blk_inv_mul (x : Matrix ι ι F) ((x⁻¹ : GL ι F) : Matrix ι ι F) e
      (Units.inv_mul x) hid.eq hcomm)

private noncomputable def cc_blk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) : GL ι F := by
  classical
  exact if h : ∃ u : GL ι F, (u : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e)
    then Classical.choose h else 1

private lemma cc_blk_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    (cc_blk x e : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e) := by
  have h : ∃ u : GL ι F, (u : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e) :=
    ⟨cc_blkAux x e hid hcomm, rfl⟩
  rw [cc_blk, dif_pos h]
  exact Classical.choose_spec h

private lemma cc_blk_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) : cc_blk x (1 : Matrix ι ι F) = x := by
  apply Units.ext
  rw [cc_blk_val x 1 IsIdempotentElem.one (by rw [mul_one, one_mul])]
  simp

private lemma cc_blk_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) : cc_blk x (0 : Matrix ι ι F) = 1 := by
  apply Units.ext
  rw [cc_blk_val x 0 IsIdempotentElem.zero (by rw [mul_zero, zero_mul])]
  simp

private lemma cc_blk_mul_add {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e f : Matrix ι ι F) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0)
    (hxe : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F))
    (hxf : (x : Matrix ι ι F) * f = f * (x : Matrix ι ι F)) :
    cc_blk x (e + f) = cc_blk x e * cc_blk x f := by
  have hsumid : IsIdempotentElem (e + f) := by
    show (e + f) * (e + f) = e + f
    noncomm_ring [he.eq, hf.eq, hef, hfe]
  have hsumcomm : (x : Matrix ι ι F) * (e + f) = (e + f) * (x : Matrix ι ι F) := by
    rw [mul_add, add_mul, hxe, hxf]
  have h5 : e * (f * (x : Matrix ι ι F)) = 0 := by
    rw [← mul_assoc, hef, zero_mul]
  have h6 : f * (e * (x : Matrix ι ι F)) = 0 := by
    rw [← mul_assoc, hfe, zero_mul]
  have h1 : e * ((x : Matrix ι ι F) * f) = 0 := by
    rw [← mul_assoc, hxe.symm, mul_assoc, hef, mul_zero]
  have h3 : f * ((x : Matrix ι ι F) * e) = 0 := by
    rw [← mul_assoc, hxf.symm, mul_assoc, hfe, mul_zero]
  have h2 : e * ((x : Matrix ι ι F) * (f * (x : Matrix ι ι F))) = 0 := by
    rw [← mul_assoc, hxe.symm, mul_assoc, ← mul_assoc e f (x : Matrix ι ι F),
      hef, zero_mul, mul_zero]
  apply Units.ext
  rw [Units.val_mul, cc_blk_val x (e + f) hsumid hsumcomm,
    cc_blk_val x e he hxe, cc_blk_val x f hf hxf]
  noncomm_ring [he.eq, hf.eq, hef, hfe, hxe, hxf, h1, h2, h3, h5, h6]

private lemma cc_blk_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x y : GL ι F) (e f : Matrix ι ι F) (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0)
    (hxe : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F))
    (hxf : (x : Matrix ι ι F) * f = f * (x : Matrix ι ι F))
    (hye : (y : Matrix ι ι F) * e = e * (y : Matrix ι ι F))
    (hyf : (y : Matrix ι ι F) * f = f * (y : Matrix ι ι F)) :
    Commute (cc_blk x e) (cc_blk y f) := by
  have h1 : e * (f * (y : Matrix ι ι F)) = 0 := by
    rw [← mul_assoc, hef, zero_mul]
  have h2 : e * (f * (x : Matrix ι ι F)) = 0 := by
    rw [← mul_assoc, hef, zero_mul]
  have h3 : e * ((x : Matrix ι ι F) * (f * (y : Matrix ι ι F))) = 0 := by
    rw [← mul_assoc, hxe.symm, mul_assoc, ← mul_assoc e f (y : Matrix ι ι F),
      hef, zero_mul, mul_zero]
  have h4 : f * (e * (x : Matrix ι ι F)) = 0 := by
    rw [← mul_assoc, hfe, zero_mul]
  have h5 : f * (e * (y : Matrix ι ι F)) = 0 := by
    rw [← mul_assoc, hfe, zero_mul]
  have h6 : f * ((y : Matrix ι ι F) * (e * (x : Matrix ι ι F))) = 0 := by
    rw [← mul_assoc, hyf.symm, mul_assoc, ← mul_assoc f e (x : Matrix ι ι F),
      hfe, zero_mul, mul_zero]
  change (cc_blk x e) * (cc_blk y f) = (cc_blk y f) * (cc_blk x e)
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, cc_blk_val x e he hxe, cc_blk_val y f hf hyf]
  noncomm_ring [he.eq, hf.eq, hef, hfe, hxe, hxf, hye, hyf, h1, h2, h3, h4, h5, h6]

private lemma cc_blk_mem_centralizer {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι]
    [Field F] (j : U →* GL ι F) (S : Set (GL ι F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (x : U)
    (hx : x ∈ (Subgroup.centralizer S).comap j) (e : Matrix ι ι F)
    (heA : e ∈ Algebra.adjoin F (Units.val '' S)) (hid : IsIdempotentElem e)
    (hxe : (j x : Matrix ι ι F) * e = e * (j x : Matrix ι ι F)) :
    cc_blk (j x) e ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, cc_blk_val (j x) e hid hxe]
  have hxs : (s : Matrix ι ι F) * (j x : Matrix ι ι F) =
      (j x : Matrix ι ι F) * (s : Matrix ι ι F) := by
    have hmem := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx)) s hs
    simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hmem
  have hes : e * (s : Matrix ι ι F) = (s : Matrix ι ι F) * e :=
    cc_adjoin_commute_S S hS e heA s hs
  have h1 : (s : Matrix ι ι F) * ((j x : Matrix ι ι F) * e) =
      (j x : Matrix ι ι F) * ((s : Matrix ι ι F) * e) := by
    rw [← mul_assoc, hxs, mul_assoc]
  noncomm_ring [hxs, hes, h1]

private lemma cc_blk_mem_glFixing {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hxe : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    cc_blk x e ∈ glFixing (1 - e) := by
  change ((cc_blk x e : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e
  rw [cc_blk_val x e hid hxe]
  have h1 : e * (e * (x : Matrix ι ι F)) = e * (x : Matrix ι ι F) := by
    rw [← mul_assoc, hid.eq]
  noncomm_ring [hid.eq, hxe, h1]

private lemma cc_mul_sum_eq_zero {ι F : Type} [Fintype ι] [Field F]
    (a : Matrix ι ι F) (T : Finset (Matrix ι ι F))
    (h : ∀ p ∈ T, a * p = 0) : a * (∑ p ∈ T, p) = 0 := by
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro p hp
  exact h p hp

private lemma cc_sum_mul_eq_zero {ι F : Type} [Fintype ι] [Field F]
    (a : Matrix ι ι F) (T : Finset (Matrix ι ι F))
    (h : ∀ p ∈ T, p * a = 0) : (∑ p ∈ T, p) * a = 0 := by
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro p hp
  exact h p hp

private lemma cc_sum_comm {ι F : Type} [Fintype ι] [Field F]
    (x : Matrix ι ι F) (T : Finset (Matrix ι ι F))
    (h : ∀ p ∈ T, x * p = p * x) :
    x * (∑ p ∈ T, p) = (∑ p ∈ T, p) * x := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  exact h p hp

private lemma cc_sum_idem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (T : Finset (Matrix ι ι F))
    (hid : ∀ p ∈ T, IsIdempotentElem p)
    (horth : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → p * q = 0) :
    IsIdempotentElem (∑ p ∈ T, p) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [IsIdempotentElem.zero]
  | insert a T ha ih =>
      rw [Finset.sum_insert ha]
      have ha_id : IsIdempotentElem a := hid a (Finset.mem_insert_self a T)
      have hT_id : ∀ p ∈ T, IsIdempotentElem p :=
        fun p hp => hid p (Finset.mem_insert_of_mem hp)
      have hT_orth : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → p * q = 0 :=
        fun p hp q hq hpq =>
          horth p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_of_mem hq) hpq
      have ihT : IsIdempotentElem (∑ p ∈ T, p) := ih hT_id hT_orth
      have haT : a * (∑ p ∈ T, p) = 0 :=
        cc_mul_sum_eq_zero a T (fun p hp =>
          horth a (Finset.mem_insert_self a T) p (Finset.mem_insert_of_mem hp)
            (fun h => ha (h.symm ▸ hp)))
      have hTa : (∑ p ∈ T, p) * a = 0 :=
        cc_sum_mul_eq_zero a T (fun p hp =>
          horth p (Finset.mem_insert_of_mem hp) a (Finset.mem_insert_self a T)
            (fun h => ha (h.symm ▸ hp)))
      show (a + ∑ p ∈ T, p) * (a + ∑ p ∈ T, p) = a + ∑ p ∈ T, p
      noncomm_ring [ha_id.eq, ihT.eq, haT, hTa]

private def cc_bracket {G : Type} [Group G] (a b : G) : G := a * b * a⁻¹ * b⁻¹

private lemma cc_commutator_mul_mul {G : Type} [Group G] (a b c d : G)
    (hac : Commute a c) (had : Commute a d) (hbc : Commute b c) (hbd : Commute b d) :
    cc_bracket (a * c) (b * d) = cc_bracket a b * cc_bracket c d := by
  have h1 : a * c * (b * d) = a * b * (c * d) := by
    rw [mul_assoc a c, ← mul_assoc c b, ← hbc.eq, mul_assoc b c, ← mul_assoc a b]
  have h2 : b * d * (a * c) = b * a * (d * c) := by
    rw [mul_assoc b d, ← mul_assoc d a, ← had.eq, mul_assoc a d, ← mul_assoc b a]
  have hc : Commute c (b * a) := hbc.symm.mul_right hac.symm
  have hd : Commute d (b * a) := hbd.symm.mul_right had.symm
  have h3 : Commute (c * d * c⁻¹ * d⁻¹) (b * a) :=
    ((hc.mul_left hd).mul_left hc.inv_left).mul_left hd.inv_left
  calc cc_bracket (a * c) (b * d)
      = a * c * (b * d) * (b * d * (a * c))⁻¹ := by rw [cc_bracket]; group
    _ = a * b * (c * d) * (b * a * (d * c))⁻¹ := by rw [h1, h2]
    _ = a * b * (c * d * c⁻¹ * d⁻¹) * (b * a)⁻¹ := by group
    _ = a * b * (b * a)⁻¹ * (c * d * c⁻¹ * d⁻¹) := by
        rw [mul_assoc (a * b), h3.inv_right.eq, ← mul_assoc]
    _ = cc_bracket a b * cc_bracket c d := by rw [cc_bracket, cc_bracket]; group

private lemma cc_bracket_mem {G : Type} [Group G] {H : Subgroup G} {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : cc_bracket a b ∈ H := by
  rw [cc_bracket]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

private lemma cc_conj_mem_glFixing {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (a b : GL ι F) (e : Matrix ι ι F)
    (hae : (a : Matrix ι ι F) * (1 - e) = (1 - e) * (a : Matrix ι ι F))
    (hbe : (b : Matrix ι ι F) * (1 - e) = 1 - e) :
    (a * b * a⁻¹ : GL ι F) ∈ glFixing (1 - e) := by
  have hai : ((a⁻¹ : GL ι F) : Matrix ι ι F) * (1 - e) =
      (1 - e) * ((a⁻¹ : GL ι F) : Matrix ι ι F) :=
    cc_inv_comm (Units.mul_inv a) (Units.inv_mul a) hae
  change ((a * b * a⁻¹ : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e
  rw [Units.val_mul, Units.val_mul]
  calc (a : Matrix ι ι F) * (b : Matrix ι ι F) * ((a⁻¹ : GL ι F) : Matrix ι ι F) * (1 - e)
      = (a : Matrix ι ι F) * ((b : Matrix ι ι F) *
          (((a⁻¹ : GL ι F) : Matrix ι ι F) * (1 - e))) := by noncomm_ring
    _ = (a : Matrix ι ι F) * ((b : Matrix ι ι F) *
          ((1 - e) * ((a⁻¹ : GL ι F) : Matrix ι ι F))) := by rw [hai]
    _ = (a : Matrix ι ι F) * (((b : Matrix ι ι F) * (1 - e)) *
          ((a⁻¹ : GL ι F) : Matrix ι ι F)) := by noncomm_ring
    _ = (a : Matrix ι ι F) * ((1 - e) * ((a⁻¹ : GL ι F) : Matrix ι ι F)) := by rw [hbe]
    _ = ((a : Matrix ι ι F) * (1 - e)) * ((a⁻¹ : GL ι F) : Matrix ι ι F) := by noncomm_ring
    _ = ((1 - e) * (a : Matrix ι ι F)) * ((a⁻¹ : GL ι F) : Matrix ι ι F) := by rw [hae]
    _ = 1 - e := by rw [mul_assoc, Units.mul_inv, mul_one]

private lemma cc_commutator_self {G : Type} [Group G] {L : Subgroup G}
    (h : commutator ↥L = ⊤) : ⁅L, L⁆ = L := by
  have hmap := Subgroup.map_subtype_commutator L
  rw [h] at hmap
  rw [← hmap]
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩

private lemma cc_not_comm_of_quasisimple {Q : Type} [Group Q]
    (h : CFSG.Assembly.IsQuasisimple Q) : ¬ ∀ a b : Q, a * b = b * a := by
  intro hcomm
  haveI : IsMulCommutative Q := ⟨⟨hcomm⟩⟩
  have hcenter : Subgroup.center Q = ⊤ := Subgroup.center_eq_top
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := h.2.toNontrivial
  haveI : Subsingleton (Q ⧸ Subgroup.center Q) := by
    rw [hcenter]
    constructor
    intro x y
    induction x using QuotientGroup.induction_on with
    | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
        rw [QuotientGroup.eq]
        exact Subgroup.mem_top _
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hxy (Subsingleton.elim x y)

private lemma cc_subgroupOf_isSubnormal {G : Type} [Group G] {H K : Subgroup G}
    (h : CFSG.Assembly.IsSubnormal H K) : (H.subgroupOf K).IsSubnormal := by
  have hopen : CFSG.Open.IsSubnormal H K := by
    induction h with
    | refl H => exact CFSG.Open.IsSubnormal.refl H
    | step hHM hnorm hMK ih => exact CFSG.Open.IsSubnormal.step hHM hnorm ih
  exact CFSG.Open.IsSubnormal.subgroupOf hopen

private lemma cc_gw_isQuasisimple {Q : Type} [Group Q]
    (h : CFSG.Assembly.IsQuasisimple Q) : CFSG.GorensteinWalter.IsQuasisimple Q := by
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := h.2.toNontrivial
  haveI : Nontrivial Q :=
    Function.Surjective.nontrivial (QuotientGroup.mk_surjective (s := Subgroup.center Q))
  exact ⟨inferInstance, h.1, h.2⟩

private lemma cc_gw_isComponentOf {G : Type} [Group G] {L K : Subgroup G}
    (h : CFSG.Assembly.IsComponentOf L K) : CFSG.GorensteinWalter.IsComponentOf L K :=
  ⟨h.1, cc_subgroupOf_isSubnormal h.2.1, cc_gw_isQuasisimple h.2.2⟩

theorem exists_isPrimStarIdemIn_isComponentOf_glBlockCentralizer
    {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    (j : U →* GL ι F) (hj : Function.Injective j) (S : Set (GL ι F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (star : Matrix ι ι F → Matrix ι ι F)
    (hone : star 1 = 1)
    (hadd : ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      star (a + b) = star a + star b)
    (hblock : ∀ ε ∈ Algebra.adjoin F (Units.val '' S), IsIdempotentElem ε → star ε = ε →
      ∀ x ∈ (Subgroup.centralizer S).comap j, ∀ y ∈ (Subgroup.centralizer S).comap j,
        ∃ w : U, (j w : Matrix ι ι F) *
          (((j x : Matrix ι ι F) * ε + (1 - ε)) * ((j y : Matrix ι ι F) * ε + (1 - ε))) =
          ((j y : Matrix ι ι F) * ε + (1 - ε)) * ((j x : Matrix ι ι F) * ε + (1 - ε)))
    {J' : Subgroup U} (hJ : IsComponentOf J' ((Subgroup.centralizer S).comap j)) :
    ∃ ε, IsPrimStarIdemIn star (Algebra.adjoin F (Units.val '' S)) ε ∧
      IsComponentOf J' ⁅glBlockCentralizer j S ε, glBlockCentralizer j S ε⁆ := by
  classical
  let A : Subalgebra F (Matrix ι ι F) := Algebra.adjoin F (Units.val '' S)
  let C : Subgroup U := (Subgroup.centralizer S).comap j
  have hcommA : ∀ x ∈ C, ∀ a ∈ A,
      (j x : Matrix ι ι F) * a = a * (j x : Matrix ι ι F) :=
    fun x hx => cc_mem_adjoin_commute j S x hx
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := cc_adjoin_comm S hS
  obtain ⟨P, hPprim, hPorth, hPsum⟩ :=
    exists_finset_isPrimStarIdemIn_sum_eq star A hAcomm hadd
      (Subalgebra.one_mem A) IsIdempotentElem.one hone
  have hpA : ∀ p ∈ P, p ∈ A := fun p hp => ((hPprim p hp).1).1
  have hpid : ∀ p ∈ P, IsIdempotentElem p := fun p hp => ((hPprim p hp).1).2.1
  have hpstar : ∀ p ∈ P, star p = p := fun p hp => ((hPprim p hp).1).2.2.2.1
  haveI hUfin : Finite U := by
    haveI : Finite (GL ι F) := inferInstance
    exact Finite.of_injective j hj
  have claim : ∀ T : Finset (Matrix ι ι F), T ⊆ P →
      ∀ x ∈ C, ∀ y ∈ C,
        ∃ w : U, w ∈ (⨆ p ∈ T, glBlockCentralizer j S p) ∧
          j w = cc_bracket (cc_blk (j y) (∑ p ∈ T, p))
            (cc_blk (j x) (∑ p ∈ T, p)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro _ x hx y hy
        refine ⟨1, Subgroup.one_mem _, ?_⟩
        rw [map_one]
        simp only [Finset.sum_empty]
        rw [cc_blk_zero, cc_blk_zero]
        simp [cc_bracket]
    | insert a T ha ih =>
        intro hTP x hx y hy
        have haP : a ∈ P := hTP (Finset.mem_insert_self a T)
        have hTP' : ∀ p, p ∈ T → p ∈ P := fun p hp => hTP (Finset.mem_insert_of_mem hp)
        have haA : a ∈ A := hpA a haP
        have ha_id : IsIdempotentElem a := hpid a haP
        have ha_star : star a = a := hpstar a haP
        have hT_id : ∀ p ∈ T, IsIdempotentElem p := fun p hp => hpid p (hTP' p hp)
        have hT_orth : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → p * q = 0 :=
          fun p hp q hq hpq => hPorth p (hTP' p hp) q (hTP' q hq) hpq
        have heT_id : IsIdempotentElem (∑ p ∈ T, p) := cc_sum_idem T hT_id hT_orth
        have haT : a * (∑ p ∈ T, p) = 0 :=
          cc_mul_sum_eq_zero a T (fun p hp =>
            hPorth a haP p (hTP' p hp) (fun h => ha (h.symm ▸ hp)))
        have hTa : (∑ p ∈ T, p) * a = 0 :=
          cc_sum_mul_eq_zero a T (fun p hp =>
            hPorth p (hTP' p hp) a haP (fun h => ha (h.symm ▸ hp)))
        have hxeT : (j x : Matrix ι ι F) * (∑ p ∈ T, p) =
            (∑ p ∈ T, p) * (j x : Matrix ι ι F) :=
          cc_sum_comm (j x) T (fun p hp => hcommA x hx p (hpA p (hTP' p hp)))
        have hyeT : (j y : Matrix ι ι F) * (∑ p ∈ T, p) =
            (∑ p ∈ T, p) * (j y : Matrix ι ι F) :=
          cc_sum_comm (j y) T (fun p hp => hcommA y hy p (hpA p (hTP' p hp)))
        have hxa : (j x : Matrix ι ι F) * a = a * (j x : Matrix ι ι F) :=
          hcommA x hx a haA
        have hya : (j y : Matrix ι ι F) * a = a * (j y : Matrix ι ι F) :=
          hcommA y hy a haA
        obtain ⟨wT, hwT_mem, hwT_eq⟩ := ih hTP' x hx y hy
        obtain ⟨wa, hwa_raw⟩ := hblock a haA ha_id ha_star x hx y hy
        have hwa_eq : j wa = cc_bracket (cc_blk (j y) a) (cc_blk (j x) a) := by
          have hblock_units : j wa * (cc_blk (j x) a * cc_blk (j y) a) =
              cc_blk (j y) a * cc_blk (j x) a := by
            apply Units.ext
            simp only [Units.val_mul]
            rw [cc_blk_val (j x) a ha_id hxa, cc_blk_val (j y) a ha_id hya]
            exact hwa_raw
          have h1 : j wa = cc_blk (j y) a * cc_blk (j x) a *
              (cc_blk (j x) a * cc_blk (j y) a)⁻¹ := by
            rw [← hblock_units]
            group
          rw [h1, cc_bracket]
          group
        have hwa_mem : wa ∈ glBlockCentralizer j S a := by
          change wa ∈ (Subgroup.centralizer S ⊓ glFixing (1 - a)).comap j
          apply Subgroup.mem_comap.mpr
          apply Subgroup.mem_inf.mpr
          constructor
          · rw [hwa_eq]
            exact cc_bracket_mem
              (cc_blk_mem_centralizer j S hS y hy a haA ha_id hya)
              (cc_blk_mem_centralizer j S hS x hx a haA ha_id hxa)
          · rw [hwa_eq]
            exact cc_bracket_mem
              (cc_blk_mem_glFixing (j y) a ha_id hya)
              (cc_blk_mem_glFixing (j x) a ha_id hxa)
        have hsum : (∑ p ∈ insert a T, p) = (∑ p ∈ T, p) + a := by
          rw [Finset.sum_insert ha, add_comm]
        have hYnew : cc_blk (j y) (∑ p ∈ insert a T, p) =
            cc_blk (j y) (∑ p ∈ T, p) * cc_blk (j y) a := by
          rw [hsum, cc_blk_mul_add (j y) (∑ p ∈ T, p) a heT_id ha_id hTa haT hyeT hya]
        have hXnew : cc_blk (j x) (∑ p ∈ insert a T, p) =
            cc_blk (j x) (∑ p ∈ T, p) * cc_blk (j x) a := by
          rw [hsum, cc_blk_mul_add (j x) (∑ p ∈ T, p) a heT_id ha_id hTa haT hxeT hxa]
        have hcommYT_Yq : Commute (cc_blk (j y) (∑ p ∈ T, p)) (cc_blk (j y) a) :=
          cc_blk_commute (j y) (j y) (∑ p ∈ T, p) a heT_id ha_id hTa haT hyeT hya hyeT hya
        have hcommXT_Xq : Commute (cc_blk (j x) (∑ p ∈ T, p)) (cc_blk (j x) a) :=
          cc_blk_commute (j x) (j x) (∑ p ∈ T, p) a heT_id ha_id hTa haT hxeT hxa hxeT hxa
        have hcommYT_Xq : Commute (cc_blk (j y) (∑ p ∈ T, p)) (cc_blk (j x) a) :=
          cc_blk_commute (j y) (j x) (∑ p ∈ T, p) a heT_id ha_id hTa haT hyeT hya hxeT hxa
        have hcommXT_Yq : Commute (cc_blk (j x) (∑ p ∈ T, p)) (cc_blk (j y) a) :=
          cc_blk_commute (j x) (j y) (∑ p ∈ T, p) a heT_id ha_id hTa haT hxeT hxa hyeT hya
        refine ⟨wT * wa, ?_, ?_⟩
        · have hle_a : glBlockCentralizer j S a ≤
              ⨆ p ∈ insert a T, glBlockCentralizer j S p := by
            apply le_iSup_of_le (f := fun p =>
              ⨆ (_ : p ∈ insert a T), glBlockCentralizer j S p) a
            apply le_iSup_of_le (f := fun _ : a ∈ insert a T =>
              glBlockCentralizer j S a) (Finset.mem_insert_self a T)
            exact le_rfl
          have hle_T : (⨆ p ∈ T, glBlockCentralizer j S p) ≤
              ⨆ p ∈ insert a T, glBlockCentralizer j S p := by
            apply iSup_le
            intro p
            apply iSup_le
            intro hp
            apply le_iSup_of_le (f := fun q =>
              ⨆ (_ : q ∈ insert a T), glBlockCentralizer j S q) p
            apply le_iSup_of_le (f := fun _ : p ∈ insert a T =>
              glBlockCentralizer j S p) (Finset.mem_insert_of_mem hp)
            exact le_rfl
          exact (⨆ p ∈ insert a T, glBlockCentralizer j S p).mul_mem
            (hle_T hwT_mem) (hle_a hwa_mem)
        · rw [map_mul, hwT_eq, hwa_eq, hYnew, hXnew,
            cc_commutator_mul_mul _ _ _ _ hcommYT_Yq hcommYT_Xq hcommXT_Yq hcommXT_Xq]
  have hGqC : ∀ q : Matrix ι ι F, glBlockCentralizer j S q ≤ C := by
    intro q
    change (Subgroup.centralizer S ⊓ glFixing (1 - q)).comap j ≤
      (Subgroup.centralizer S).comap j
    exact Subgroup.comap_mono inf_le_left
  have hNC : (⨆ p ∈ P, glBlockCentralizer j S p) ≤ C := by
    apply iSup_le
    intro p
    apply iSup_le
    intro hp
    exact hGqC p
  have hab : ∀ a ∈ C, ∀ b ∈ C, a * b * a⁻¹ * b⁻¹ ∈
      (⨆ p ∈ P, glBlockCentralizer j S p) := by
    intro a ha b hb
    obtain ⟨w, hw_mem, hw_eq⟩ := claim P (fun _ h => h) b hb a ha
    have hw : w = a * b * a⁻¹ * b⁻¹ := by
      apply hj
      simpa [cc_bracket, map_mul, hPsum, cc_blk_one] using hw_eq
    simpa [hw] using hw_mem
  have hcompN : IsComponentOf J' (⨆ p ∈ P, glBlockCentralizer j S p) :=
    (CFSG.StandardType.ClassicalPosition.isComponentOf_iff_of_normal_of_commutator_le
      hNC hab).mp hJ
  have hCnorm : ∀ p ∈ P, C ≤ Subgroup.normalizer (glBlockCentralizer j S p : Set U) := by
    intro p hp
    rw [Subgroup.le_normalizer_iff]
    intro c hc g hg
    have hg' : j g ∈ Subgroup.centralizer S ⊓ glFixing (1 - p) := Subgroup.mem_comap.mp hg
    have hgC : j g ∈ Subgroup.centralizer S := hg'.1
    have hgF : j g ∈ glFixing (1 - p) := hg'.2
    have hconj : j (c * g * c⁻¹) = j c * j g * (j c)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    change j (c * g * c⁻¹) ∈ (Subgroup.centralizer S ⊓ glFixing (1 - p))
    rw [hconj]
    apply Subgroup.mem_inf.mpr
    constructor
    · have hcC : j c ∈ Subgroup.centralizer S := Subgroup.mem_comap.mp hc
      exact (Subgroup.centralizer S).mul_mem
        ((Subgroup.centralizer S).mul_mem hcC hgC) ((Subgroup.centralizer S).inv_mem hcC)
    · have hce : (j c : Matrix ι ι F) * (1 - p) =
          (1 - p) * (j c : Matrix ι ι F) := by
        have := hcommA c hc p (hpA p hp)
        noncomm_ring [this]
      exact cc_conj_mem_glFixing (j c) (j g) p hce hgF
  have hGpN : ∀ p ∈ P, glBlockCentralizer j S p ≤
      (⨆ q ∈ P, glBlockCentralizer j S q) := by
    intro p hp
    apply le_iSup_of_le (f := fun q =>
      ⨆ (_ : q ∈ P), glBlockCentralizer j S q) p
    apply le_iSup_of_le (f := fun _ : p ∈ P => glBlockCentralizer j S p) hp
    exact le_rfl
  have hNnorm : ∀ p ∈ P, (⨆ q ∈ P, glBlockCentralizer j S q) ≤
      Subgroup.normalizer (glBlockCentralizer j S p : Set U) := by
    intro p hp
    apply iSup_le
    intro q
    apply iSup_le
    intro hq
    exact le_trans (hGqC q) (hCnorm p hp)
  have hper : ∀ p ∈ P, J' ≤ glBlockCentralizer j S p ∨
      ⁅J', glBlockCentralizer j S p⁆ = ⊥ := by
    intro p hp
    exact CFSG.Walter.isComponentOf_le_or_commutator_eq_bot
      (cc_gw_isComponentOf hcompN) (hGpN p hp) (hNnorm p hp)
  by_cases hsome : ∃ p ∈ P, J' ≤ glBlockCentralizer j S p
  · obtain ⟨p, hpP, hp_le⟩ := hsome
    refine ⟨p, (hPprim p hpP).1, ?_⟩
    have hJGp : IsComponentOf J' (glBlockCentralizer j S p) :=
      CFSG.Assembly.IsComponentOf.of_le_of_le hcompN hp_le (hGpN p hpP)
    have hJperf : ⁅J', J'⁆ = J' := cc_commutator_self hJ.2.2.1
    have hJleComm : J' ≤ ⁅glBlockCentralizer j S p, glBlockCentralizer j S p⁆ := by
      calc J' = ⁅J', J'⁆ := hJperf.symm
        _ ≤ ⁅glBlockCentralizer j S p, glBlockCentralizer j S p⁆ :=
            Subgroup.commutator_mono hp_le hp_le
    exact CFSG.Assembly.IsComponentOf.of_le_of_le hJGp hJleComm
      (Subgroup.commutator_le_self _)
  · have hsome' : ∀ p, p ∈ P → ¬ J' ≤ glBlockCentralizer j S p := by
      intro p hp hle
      exact hsome ⟨p, hp, hle⟩
    have hbot : ∀ p ∈ P, ⁅J', glBlockCentralizer j S p⁆ = ⊥ := by
      intro p hp
      rcases hper p hp with hle | hbot
      · exact absurd hle (hsome' p hp)
      · exact hbot
    have hcommAll : ∀ a ∈ J', ∀ b ∈ (⨆ p ∈ P, glBlockCentralizer j S p),
        a * b = b * a := by
      intro a ha b hb
      refine Subgroup.iSup_induction
        (S := fun p => ⨆ (_ : p ∈ P), glBlockCentralizer j S p)
        (C := fun y => a * y = y * a) hb ?_ ?_ ?_
      · intro p y hy
        refine Subgroup.iSup_induction (S := fun (_ : p ∈ P) =>
          glBlockCentralizer j S p) (C := fun y => a * y = y * a) hy ?_ ?_ ?_
        · intro hp z hz
          have hle_cent : J' ≤ Subgroup.centralizer
              ↑(glBlockCentralizer j S p) :=
            (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (hbot p hp)
          exact ((Subgroup.mem_centralizer_iff.mp (hle_cent ha)) z hz).symm
        · rw [mul_one, one_mul]
        · intro x y hx hy
          rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
      · rw [mul_one, one_mul]
      · intro x y hx hy
        rw [← mul_assoc, hx, mul_assoc, hy, ← mul_assoc]
    have hJabel : ∀ a b : ↥J', a * b = b * a := by
      intro a b
      apply Subtype.ext
      exact hcommAll a a.2 b (hcompN.1 b.2)
    exfalso
    exact (cc_not_comm_of_quasisimple hJ.2.2) hJabel

end CFSG.StandardType.ClassicalPosition.Block
