module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTorus
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitLayer
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitComp
import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux6

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

variable {G : Type} [Group G] [Finite G]

structure QTwoUnitDel (Bs : Subgroup G) {m : ℕ} (βL : Additive ↥Bs ≃+ DVec m) (a b c : Fin m)
    (α : MulAut ↥Bs) (g : G) (b' : ↥Bs) : Prop where
  hab : a ≠ b
  hca : c ≠ a
  hcb : c ≠ b
  sign : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign m a b (βL (Additive.ofMul s))
  norm : g ∈ Subgroup.normalizer (Bs : Set G)
  conj : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹
  coord : βL (Additive.ofMul b') = Pi.single c 1

noncomputable abbrev qtwoDelJ {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}
    (ψ : Su F0 2 1 m →* G) (c : Fin m) : Subgroup G :=
  (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ

noncomputable abbrev qtwoDelX {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {m : ℕ}
    (ψ : Su F0 2 1 m →* G) (c : Fin m) (g : G) : Subgroup G :=
  qtwoDelJ ψ c ⊔ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem qtwoDB16_dSign_single {m : ℕ} {a b c : Fin m} (hca : c ≠ a) (hcb : c ≠ b) :
    dSign m a b (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
  have hsingle : Pi.single c (1 : ZMod 3) = dBasis m c :=
    (Pi.basisFun_apply (ZMod 3) (Fin m) c).symm
  have hnot : ¬ (c = a ∨ c = b) := by tauto
  have hfix : dSign m a b (dBasis m c) = dBasis m c := by
    rw [dSign_apply, if_neg hnot, one_smul]
  rw [hsingle, hfix]

theorem qtwoDB16_sum_dBasis_eq_one (m : ℕ) :
    (∑ j, dBasis m j) = (1 : DVec m) := by
  funext k
  rw [Finset.sum_apply]
  simp [dBasis, Pi.basisFun_apply, Pi.single_apply]

theorem qtwoDB16_dSign_one_apply (m : ℕ) (a b i : Fin m) :
    dSign m a b (1 : DVec m) i = if i = a ∨ i = b then (-1 : ZMod 3) else 1 := by
  have h1 : (1 : DVec m) = ∑ j, dBasis m j := (qtwoDB16_sum_dBasis_eq_one m).symm
  have hsum : dSign m a b (1 : DVec m) = ∑ j, dSign m a b (dBasis m j) := by
    rw [h1]
    simp only [map_sum]
  rw [hsum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · rw [dSign_apply]
    simp only [Pi.smul_apply, dBasis, Pi.basisFun_apply, Pi.single_eq_same, smul_eq_mul,
      mul_one]
  · intro j _ hj
    rw [dSign_apply]
    simp [dBasis, Pi.basisFun_apply, Pi.single_apply, Ne.symm hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem qtwoDB16_mem_span_of_mem_closure {P : Submodule (ZMod 3) (DVec m)}
    {a₁ a₂ : ↥Bs} (ha₁ : βL (Additive.ofMul a₁) ∈ P) (ha₂ : βL (Additive.ofMul a₂) ∈ P)
    {t : ↥Bs} (ht : (t : G) ∈ Subgroup.closure {(a₁ : G), (a₂ : G)}) :
    βL (Additive.ofMul t) ∈ P := by
  let T : Subgroup ↥Bs :=
    { carrier := {t | βL (Additive.ofMul t) ∈ P}
      one_mem' := by
        show βL (0 : Additive ↥Bs) ∈ P
        rw [map_zero]
        exact P.zero_mem
      mul_mem' := by
        intro u v hu hv
        change βL (Additive.ofMul u + Additive.ofMul v) ∈ P
        rw [map_add]
        exact P.add_mem hu hv
      inv_mem' := by
        intro u hu
        change βL (- Additive.ofMul u) ∈ P
        rw [map_neg]
        exact P.neg_mem hu }
  have hTK : Subgroup.closure {(a₁ : G), (a₂ : G)} ≤ T.map (Subgroup.subtype Bs) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ⟨a₁, ha₁, rfl⟩
    · exact ⟨a₂, ha₂, rfl⟩
  obtain ⟨u, huT, huG⟩ := hTK ht
  rwa [Subtype.ext huG] at huT

theorem qtwoDB16_map_conj_J_le (hbase : QTwoUnitBase p B Bs x L ψ ε) {s : G}
    (hs : s ∈ Bs) :
    (qtwoDelJ ψ c).map (MulAut.conj s).toMonoidHom ≤ qtwoDelJ ψ c := by
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨g, hgdiag, -, hact⟩ := hbase.diag s hs
  obtain ⟨B, hBA, hBs⟩ := hact A
  change s * ψ A * s⁻¹ ∈ qtwoDelJ ψ c
  rw [hBs]
  refine Subgroup.mem_map.mpr ⟨B, ?_, rfl⟩
  obtain ⟨d, hd⟩ := hgdiag
  rw [mem_coordBlockSU_iff_indicator]
  set Gm : Matrix (Fin m) (Fin m) F0 := ((g : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
    with hGm
  set Gim : Matrix (Fin m) (Fin m) F0 := (((g⁻¹ : GL (Fin m) F0)) : Matrix (Fin m) (Fin m) F0)
    with hGim
  set Am : Matrix (Fin m) (Fin m) F0 := ((A : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
    with hAm
  set P : Matrix (Fin m) (Fin m) F0 := compIndicator F0 (Finset.univ.erase c) with hP
  have hPAm : P * Am = P := (mem_coordBlockSU_iff_indicator.mp hA).1
  have hAmP : Am * P = P := (mem_coordBlockSU_iff_indicator.mp hA).2
  have hGmGim : Gm * Gim = 1 := by
    rw [hGm, hGim, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGimGm : Gim * Gm = 1 := by
    rw [hGm, hGim, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGmd : Gm = Matrix.diagonal d := by rw [hGm]; exact hd
  have hPcomm : P * Gm = Gm * P := by
    rw [hP, hGmd, compIndicator, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_comm]
  have hPG : P * Gim = Gim * P := by
    calc P * Gim = (Gim * Gm) * P * Gim := by rw [hGimGm, one_mul]
      _ = Gim * (Gm * P) * Gim := by simp only [mul_assoc]
      _ = Gim * (P * Gm) * Gim := by rw [hPcomm]
      _ = Gim * P * (Gm * Gim) := by simp only [mul_assoc]
      _ = Gim * P := by rw [hGmGim, mul_one]
  have hBmat : ((B : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Gm * Am * Gim := by
    have h1 := congrArg (fun z : GL (Fin m) F0 => ((z : Matrix (Fin m) (Fin m) F0))) hBA
    rw [hGm, hAm, hGim]
    simpa [Units.val_mul] using h1
  constructor
  · rw [hBmat]
    calc P * (Gm * Am * Gim) = (P * Gm) * Am * Gim := by simp only [mul_assoc]
      _ = (Gm * P) * Am * Gim := by rw [hPcomm]
      _ = Gm * (P * Am) * Gim := by simp only [mul_assoc]
      _ = Gm * P * Gim := by rw [hPAm]
      _ = Gm * (P * Gim) := by simp only [mul_assoc]
      _ = Gm * (Gim * P) := by rw [hPG]
      _ = (Gm * Gim) * P := by simp only [mul_assoc]
      _ = P := by rw [hGmGim, one_mul]
  · rw [hBmat]
    calc (Gm * Am * Gim) * P = Gm * (Am * (Gim * P)) := by simp only [mul_assoc]
      _ = Gm * (Am * (P * Gim)) := by rw [hPG]
      _ = Gm * ((Am * P) * Gim) := by simp only [mul_assoc]
      _ = Gm * (P * Gim) := by rw [hAmP]
      _ = Gm * (Gim * P) := by rw [hPG]
      _ = (Gm * Gim) * P := by simp only [mul_assoc]
      _ = P := by rw [hGmGim, one_mul]

theorem qtwoDB16_J_perfect (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε) :
    qtwoDelJ ψ c ≤ ⁅qtwoDelJ ψ c, qtwoDelJ ψ c⁆ := by
  obtain ⟨θ, hθinj, hθrange, -⟩ := ggQTwoDUnit_J_iso (by omega) hbase c 1
  have hperf_su : Group.IsPerfect (Su F0 2 1 (m - 1)) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid
      (CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1)
        (by simpa using hbase.card_field))
      (by omega) (fun h => absurd h (by omega))
  haveI : Group.IsPerfect (Su F0 2 1 (m - 1)) := hperf_su
  let θ' : Su F0 2 1 (m - 1) →* ↥(qtwoDelJ ψ c) :=
    θ.codRestrict (qtwoDelJ ψ c) (fun u => hθrange.le (MonoidHom.mem_range.mpr ⟨u, rfl⟩))
  have hθ'surj : Function.Surjective θ' := by
    intro z
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp (hθrange.ge z.2)
    exact ⟨u, Subtype.ext hu⟩
  have hJperf : Group.IsPerfect ↥(qtwoDelJ ψ c) :=
    Group.IsPerfect.ofSurjective (f := θ') hθ'surj
  exact le_of_eq (Subgroup.isPerfect_iff.mp hJperf).symm

theorem qtwoDB16_J_order_three (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε) :
    ∃ u ∈ qtwoDelJ ψ c, u ≠ 1 ∧ u ^ 3 = 1 := by
  obtain ⟨θ, hθinj, hθrange, -⟩ := ggQTwoDUnit_J_iso (by omega) hbase c 1
  have hcard : Nat.card ↥(qtwoDelJ ψ c) = Nat.card (Su F0 2 1 (m - 1)) := by
    change Nat.card ↥((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ) =
      Nat.card (Su F0 2 1 (m - 1))
    rw [← hθrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hθinj,
      Subgroup.card_top]
  have hdiv : 3 ∣ Nat.card (Su F0 2 1 (m - 1)) := by
    let J : Finset (Fin (m - 1)) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
    have hJ : J.card = 3 := by
      change ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩} :
        Finset (Fin (m - 1))).card = 3
      rw [Finset.card_triple_eq_three_iff]
      refine ⟨?_, ?_, ?_⟩ <;>
        (intro h; exact absurd (congrArg Fin.val h) (by norm_num))
    have h216 : Nat.card ↥(coordBlockSU F0 2 1 J) = 216 :=
      qTwoS34_card_coordBlockSU_three (K := F0) hbase.card_field hJ
    have hle : coordBlockSU F0 2 1 J ≤ (⊤ : Subgroup (Su F0 2 1 (m - 1))) := le_top
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_top] at hdvd
    exact dvd_trans (by rw [h216]; norm_num) hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(qtwoDelJ ψ c)) 3
    (by rw [hcard]; exact hdiv)
  refine ⟨(u : G), u.2, ?_, ?_⟩
  · intro h
    have hu1 : u = 1 := Subtype.ext h
    rw [hu1, orderOf_one] at hu
    omega
  · have hu3 : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    simpa using congrArg Subtype.val hu3

end CFSG.StandardType.QTwo

end
