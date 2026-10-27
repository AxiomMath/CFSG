module

public import CFSG.Monster.Schur.GmatStructureVec
public import CFSG.Monster.Schur.H1Hvis
public import CFSG.Monster.Schur.LemmaA
public import CFSG.Monster.Schur.GmatStructureZ

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Schur

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Visible CFSG.Monster.VisQuot
  CFSG.Monster.VisCert CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.B Subgroup
open scoped IsMulCommutative commutatorElement

theorem finrank_L2 : Module.finrank (ZMod 2) L2 = 24 :=
  visModLat.finrank_eq.symm.trans finrank_visMod

section

variable {E : Type} [Group E] (π : E →* SpaceB ≃ₗ[ℚ] SpaceB)

@[expose] def Chat : Subgroup E := Gvis.comap π

@[expose] def Phat : Subgroup (Chat π) := (Qmat.comap π).subgroupOf (Chat π)

@[expose] def pChat :
    Chat π →* Hvis := PhiH.comp (π.subgroupComap Gvis)

theorem mem_Phat {x : Chat π} : x ∈ Phat π ↔ π (x : E) ∈ Qmat := Iff.rfl

theorem coe_pChat
    (c : Chat π) : ((pChat π c : Hvis) : GLV) = PhiV ⟨π (c : E), c.2⟩ := rfl

theorem ker_pChat :
    (pChat π).ker = Phat π := by
  ext c
  rw [MonoidHom.mem_ker, mem_Phat]
  constructor
  · intro h
    have h1 : PhiV ⟨π (c : E), c.2⟩ = 1 := by
      have := congrArg (fun a : Hvis => (a : GLV)) h
      exact this
    exact PhiV_eq_one_iff.1 h1
  · intro h
    exact Subtype.ext (PhiV_eq_one_iff.2 h)

theorem pChat_surjective
    (hrange : π.range = Gmat) : Function.Surjective (pChat π) := by
  intro ν
  obtain ⟨g, hg⟩ := PhiH_surjective ν
  have hgG : (g : SpaceB ≃ₗ[ℚ] SpaceB) ∈ π.range := by
    rw [hrange]
    exact Hmat_le_Gmat g.2
  obtain ⟨e, he⟩ := hgG
  have heC : e ∈ Chat π := by
    show π e ∈ Gvis
    rw [he]
    exact g.2
  refine ⟨⟨e, heC⟩, ?_⟩
  rw [← hg]
  show PhiH (π.subgroupComap Gvis ⟨e, heC⟩) = PhiH g
  rw [show π.subgroupComap Gvis ⟨e, heC⟩ = g from Subtype.ext he]

instance normal_Phat : (Phat π).Normal where
  conj_mem := by
    intro x hx g
    rw [mem_Phat] at hx ⊢
    show π ((g : E) * (x : Chat π) * (g : E)⁻¹) ∈ Qmat
    rw [map_mul, map_mul, map_inv]
    exact norm_Qmat _ g.2 _ hx

@[expose] def vecP (x : Phat π) : L2 :=
  vecQ ⟨π ((x : Chat π) : E), (mem_Phat π).1 x.2⟩

theorem vecP_mul (x y : Phat π) : vecP π (x * y) = vecP π x + vecP π y := by
  unfold vecP
  have : (⟨π (((x * y : Phat π) : Chat π) : E), (mem_Phat π).1 (x * y).2⟩ : Qmat) =
      ⟨π ((x : Chat π) : E), (mem_Phat π).1 x.2⟩ *
        ⟨π ((y : Chat π) : E), (mem_Phat π).1 y.2⟩ :=
    Subtype.ext (map_mul π _ _)
  rw [this, vecQ_mul]

theorem vecP_conj
    (c : Chat π) (x : Phat π) :
    vecP π (MulAut.conjNormal c x) = hvisRep (pChat π c) (vecP π x) := by
  have hgq : π (c : E) * π ((x : Chat π) : E) * (π (c : E))⁻¹ ∈ Qmat := by
    have := (mem_Phat π).1 (MulAut.conjNormal c x).2
    rw [MulAut.conjNormal_apply] at this
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using this
  have h := vecQ_conj ⟨π (c : E), c.2⟩ ⟨π ((x : Chat π) : E), (mem_Phat π).1 x.2⟩ hgq
  rw [hvisRep_apply, coe_pChat]
  have e : (⟨π (((MulAut.conjNormal c x : Phat π) : Chat π) : E),
      (mem_Phat π).1 (MulAut.conjNormal c x).2⟩ : Qmat) =
      ⟨π (c : E) * π ((x : Chat π) : E) * (π (c : E))⁻¹, hgq⟩ := by
    apply Subtype.ext
    show π (((c * (x : Chat π) * c⁻¹ : Chat π)) : E) = _
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  unfold vecP
  rw [e]
  exact h

theorem vecP_surjective (hrange : π.range = Gmat) : Function.Surjective (vecP π) := by
  intro v
  obtain ⟨q, rfl⟩ := vecQ_surjective v
  have hq : (q : SpaceB ≃ₗ[ℚ] SpaceB) ∈ π.range := by
    rw [hrange]
    exact (Qmat_le_Hmat.trans Hmat_le_Gmat) q.2
  obtain ⟨e, he⟩ := hq
  have heC : e ∈ Chat π := by
    show π e ∈ Gvis
    rw [he]
    exact Qmat_le_Hmat q.2
  have heP : (⟨e, heC⟩ : Chat π) ∈ Phat π := by
    show π e ∈ Qmat
    rw [he]
    exact q.2
  exact ⟨⟨⟨e, heC⟩, heP⟩, congrArg vecQ (Subtype.ext he)⟩

theorem vecP_eq_zero_iff {n : E} (hπ : CentralKernel π n) {zh : E} (hzh : π zh = xmat)
    (x : Phat π) :
    vecP π x = 0 ↔ ((x : Chat π) : E) = 1 ∨ ((x : Chat π) : E) = n ∨ ((x : Chat π) : E) = zh ∨
      ((x : Chat π) : E) = zh * n := by
  unfold vecP
  rw [vecQ_eq_zero_iff]
  show π ((x : Chat π) : E) = 1 ∨ π ((x : Chat π) : E) = xmat ↔ _
  have hπn : π n = 1 := MonoidHom.mem_ker.1 (by rw [hπ.ker]; exact mem_zpowers n)
  constructor
  · rintro (h | h)
    · have : ((x : Chat π) : E) ∈ zpowers n := by
        rw [← hπ.ker]
        exact h
      rcases hπ.eq_one_or_eq_of_mem_zpowers this with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · rcases hπ.eq_or_eq_mul_of_map_eq (hzh.trans h.symm) with h1 | h1
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr h1))
  · rintro (h | h | h | h)
    · left
      rw [h, map_one]
    · left
      rw [h, hπn]
    · right
      rw [h, hzh]
    · right
      rw [h, map_mul, hzh, hπn, mul_one]

theorem mem_zpowers_mk_iff {n : E} (hnC : n ∈ Chat π) (c : Chat π) :
    c ∈ zpowers (⟨n, hnC⟩ : Chat π) ↔ (c : E) ∈ zpowers n := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem π_comm (a b : Chat π) :
    π (((⁅a, b⁆ : Chat π)) : E) = ⁅π (a : E), π (b : E)⁆ := by
  simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]

theorem vecP_eq_zero_iff_comm {n : E} (hπ : CentralKernel π n) (hnC : n ∈ Chat π)
    (hrange : π.range = Gmat) (x : Phat π) :
    vecP π x = 0 ↔ ∀ y : Phat π, ⁅(x : Chat π), (y : Chat π)⁆ ∈ zpowers (⟨n, hnC⟩ : Chat π) := by
  have hext := isExtraspecialAmbient_Qmat
  unfold vecP
  rw [vecQ_eq_zero_iff]
  show π ((x : Chat π) : E) = 1 ∨ π ((x : Chat π) : E) = xmat ↔ _
  have hxQ : π ((x : Chat π) : E) ∈ Qmat := (mem_Phat π).1 x.2
  constructor
  · intro hx y
    rw [mem_zpowers_mk_iff, ← hπ.ker, MonoidHom.mem_ker]
    show π (((⁅(x : Chat π), (y : Chat π)⁆ : Chat π)) : E) = 1
    rw [π_comm, commutatorElement_def]
    have hyQ : π ((y : Chat π) : E) ∈ Qmat := (mem_Phat π).1 y.2
    rcases hx with h | h
    · rw [h]
      group
    · rw [h]
      have hc : π ((y : Chat π) : E) * xmat = xmat * π ((y : Chat π) : E) := hext.central _ hyQ
      calc xmat * π ((y : Chat π) : E) * xmat⁻¹ * (π ((y : Chat π) : E))⁻¹
          = (xmat * π ((y : Chat π) : E)) * xmat⁻¹ * (π ((y : Chat π) : E))⁻¹ := rfl
        _ = (π ((y : Chat π) : E) * xmat) * xmat⁻¹ * (π ((y : Chat π) : E))⁻¹ := by rw [hc]
        _ = 1 := by group
  · intro h
    refine hext.center _ hxQ fun q hq => ?_
    obtain ⟨e, he⟩ : q ∈ π.range := by
      rw [hrange]
      exact (Qmat_le_Hmat.trans Hmat_le_Gmat) hq
    have heC : e ∈ Chat π := by
      show π e ∈ Gvis
      rw [he]
      exact Qmat_le_Hmat hq
    have heP : (⟨e, heC⟩ : Chat π) ∈ Phat π := by
      show π e ∈ Qmat
      rw [he]
      exact hq
    have h1 := h ⟨⟨e, heC⟩, heP⟩
    rw [mem_zpowers_mk_iff, ← hπ.ker, MonoidHom.mem_ker] at h1
    have h2 : π (((⁅(x : Chat π), ⟨e, heC⟩⁆ : Chat π)) : E) = 1 := h1
    rw [π_comm, commutatorElement_def] at h2
    show π ((x : Chat π) : E) * q = q * π ((x : Chat π) : E)
    have h3 : π ((⟨e, heC⟩ : Chat π) : E) = q := he
    rw [h3] at h2
    calc π ((x : Chat π) : E) * q = (π ((x : Chat π) : E) * q * (π ((x : Chat π) : E))⁻¹ * q⁻¹) *
          (q * π ((x : Chat π) : E)) := by group
      _ = q * π ((x : Chat π) : E) := by rw [h2, one_mul]

end

theorem lemmaAConclusion_Gmat :
    LemmaAConclusion Gmat Qmat Hmat := by
  intro E _ π n hπ hrange
  have hπn : π n = 1 := MonoidHom.mem_ker.1 (by rw [hπ.ker]; exact mem_zpowers n)
  have hnC : n ∈ Chat π := by
    show π n ∈ Gvis
    rw [hπn]
    exact one_mem _
  obtain ⟨zh, hzh⟩ : xmat ∈ π.range := by
    rw [hrange]
    exact Hmat_le_Gmat (Qmat_le_Hmat xmat_mem_Qmat)
  have hzhC : zh ∈ Chat π := by
    show π zh ∈ Gvis
    rw [hzh]
    exact Qmat_le_Hmat xmat_mem_Qmat
  have hnP : (⟨n, hnC⟩ : Chat π) ∈ Phat π := by
    show π n ∈ Qmat
    rw [hπn]
    exact one_mem _
  have hzhP : (⟨zh, hzhC⟩ : Chat π) ∈ Phat π := by
    show π zh ∈ Qmat
    rw [hzh]
    exact xmat_mem_Qmat
  have := perfect_Hvis
  have hQ := exists_unique_invariant_complement (E := Chat π) (Γ := Hvis) (V := L2) (Phat π)
    (pChat π) (pChat_surjective π hrange) (ker_pChat π) hvisRep
    (by rw [finrank_L2]; norm_num) ⟨n, hnC⟩ ⟨zh, hzhC⟩
    (Subgroup.mem_center_iff.2 fun g => Subtype.ext (hπ.comm_n g))
    (Subtype.ext hπ.mul_self) (fun h => hπ.ne_one (congrArg Subtype.val h)) hnP hzhP
    (fun h => by
      have h' : zh = 1 := congrArg Subtype.val h
      exact xmat_ne_one (by rw [← hzh, h', map_one]))
    (fun h => by
      have h' : zh = n := congrArg Subtype.val h
      exact xmat_ne_one (by rw [← hzh, h', hπn]))
    (vecP π) (vecP_mul π) (vecP_conj π) (vecP_surjective π hrange)
    (fun x => by
      rw [vecP_eq_zero_iff π hπ hzh]
      simp only [Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_one])
    (fun x => vecP_eq_zero_iff_comm π hπ hnC hrange x)
    irreducible_Hvis_L2 end_Hvis_L2 h1_Hvis_dual
  obtain ⟨Q, ⟨hQle, hQinv, hQinf, hQsup⟩, -⟩ := hQ
  have hinj : Function.Injective (Chat π).subtype := Subtype.val_injective
  have hzn : (zpowers (⟨n, hnC⟩ : Chat π)).map (Chat π).subtype = zpowers n := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hQC : Qmat.comap π ≤ Chat π := fun e he => Qmat_le_Hmat he
  refine ⟨Q.map (Chat π).subtype, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact (mem_Phat π).1 (hQle hq)
  · rw [← hzn, ← Subgroup.map_inf _ _ _ hinj, hQinf, Subgroup.map_bot]
  · rw [← hzn, ← Subgroup.map_sup, hQsup]
    exact Subgroup.map_subgroupOf_eq_of_le hQC
  · intro c hc s hs
    obtain ⟨q, hq, rfl⟩ := hs
    exact ⟨⟨c, hc⟩ * q * ⟨c, hc⟩⁻¹, hQinv ⟨c, hc⟩ q hq, rfl⟩

end CFSG.Monster.Schur
