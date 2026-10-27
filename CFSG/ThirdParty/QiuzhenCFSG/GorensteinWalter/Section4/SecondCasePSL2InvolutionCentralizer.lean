module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2Action
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2InnerReflection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2Subgroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2DihedralProjection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The `hAcont` transport for the second-case PSL₂ action

For the image `A = f[C]` of the local involution centralizer
`C = C_G(c.t) ∩ M` under the PSL₂ action `f`, prove that the PSL-range
centralizer of `τ = f(t)` is contained in `A`.

The proof: an element `x = f m` of `C(τ) ∩ pslRange` centralizes `τ`, so
`f (m t m⁻¹) = f t`; the conjugate `j = m t m⁻¹` lies in the component
`E`, `j t⁻¹ ∈ ker f ∩ E`, and `ker f ∩ E ≤ Z(E)` (the kernel is odd,
while `2 ∣ |E|`, so the normal subgroup `kerE` of the quasisimple group
`E` is not the whole of `E` and must lie in the center).  Since `j` and
`t` are involutions, `j t⁻¹` is an involution in `Z(E)`; but `Z(E)` has
odd order, so `j = t`, i.e. `m` centralizes `c.t` and `x ∈ A`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

/-- For the image `A := f[C]` of the local involution centralizer
`C := C_G(c.t) ∩ M` under the PSL₂ action `f`, with `τ := f(t)`, the
field component `τ` lies in the PSL range, `A` centralizes `τ`, and the
PSL-range centralizer of `τ` is contained in `A`. -/
public theorem secondCase_psl2_hAcont
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K) :
    let tM : ↥w.M := ⟨c.t, d.E_component.1 d.t_mem_E⟩
    let tau : PGammaL2 K := ad.f tM
    let C : Subgroup (↥w.M) :=
      (Subgroup.centralizer ({c.t} : Set G)).comap w.M.subtype
    let A : Subgroup (PGammaL2 K) := C.map ad.f
    tau ∈ pGammaL2PSLRange K ∧
      A ≤ Subgroup.centralizer ({tau} : Set (PGammaL2 K)) ∧
      (Subgroup.centralizer ({tau} : Set (PGammaL2 K)) ⊓
        pGammaL2PSLRange K) ≤ A := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let f := ad.f
  let tM : w.M := ⟨c.t, d.E_component.1 d.t_mem_E⟩
  let tE : d.E := ⟨c.t, d.t_mem_E⟩
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  let t0 : PSL2 K := ad.modelEquiv.some (q tE)
  let psl2ToPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)
  let tau : PGammaL2 K := f tM
  let C : Subgroup w.M :=
    (Subgroup.centralizer ({c.t} : Set G)).comap w.M.subtype
  let A : Subgroup (PGammaL2 K) := C.map f
  let iEM : ↥d.E →* w.M :=
    d.E.subtype.codRestrict w.M (fun x => d.E_component.1 x.2)
  let kerE : Subgroup (↥d.E) := f.ker.comap iEM
  -- τ = inl (toPGL t0)
  have hid : f tM = SemidirectProduct.inl (psl2ToPGL t0) := by
    have hact : pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree (f tM) =
        MulAut.conj t0 := by
      apply MulEquiv.ext
      intro x
      obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (Subgroup.center d.E)
        (ad.modelEquiv.some.symm x)
      have hx : x = ad.modelEquiv.some (q z) := by
        calc
          x = ad.modelEquiv.some (ad.modelEquiv.some.symm x) := by simp
          _ = ad.modelEquiv.some (q z) := congrArg ad.modelEquiv.some hz.symm
      rw [hx]
      rw [ad.action_eq tM z]
      have hq : q (⟨(tM : G) * (z : G) * (tM : G)⁻¹,
          d.E_normal.2 (tM : G) tM.2 (z : G) z.2⟩ : d.E) =
          q tE * q z * (q tE)⁻¹ := by
        have hsub : (⟨(tM : G) * (z : G) * (tM : G)⁻¹,
            d.E_normal.2 (tM : G) tM.2 (z : G) z.2⟩ : d.E) = tE * z * tE⁻¹ := by
          apply Subtype.ext
          rfl
        rw [hsub]
        rw [map_mul, map_mul, map_inv]
      rw [hq]
      simpa [t0, MulAut.conj_apply, mul_assoc]
    have hinl : pGammaL2ToMulAutPSL2 K ad.primePower ad.fieldCardGtThree
        (SemidirectProduct.inl (psl2ToPGL t0)) = MulAut.conj t0 := by
      rw [pGammaL2ToMulAutPSL2_inl]
      exact pgl2InnerAutPSL2_toPGL K ad.primePower ad.fieldCardGtThree t0
    exact pGammaL2ToMulAutPSL2_injective K ad.primePower ad.fieldCardGtThree
      (by rw [hact, hinl])
  have htauL : tau ∈ pGammaL2PSLRange K := by
    change f tM ∈ pGammaL2PSLRange K
    rw [hid]
    exact (mem_pGammaL2PSLRange_iff K (SemidirectProduct.inl (psl2ToPGL t0))).mpr ⟨t0, rfl⟩
  -- hAcent : A ≤ C(τ)
  have hAcent : A ≤ Subgroup.centralizer ({tau} : Set (PGammaL2 K)) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨m, hm, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzt : z = tau := by simpa using hz
    rw [hzt]
    change (f tM * f m : PGammaL2 K) = (f m * f tM : PGammaL2 K)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change (c.t : G) * (m : G) = (m : G) * c.t
    have hmc : (m : G) ∈ Subgroup.centralizer ({c.t} : Set G) :=
      Subgroup.mem_comap.mp hm
    exact hmc c.t (by simp)
  -- hAcont : C(τ) ∩ pslRange ≤ A
  have hAcont : (Subgroup.centralizer ({tau} : Set (PGammaL2 K)) ⊓
      pGammaL2PSLRange K) ≤ A := by
    intro x hx
    have hxcent : x ∈ Subgroup.centralizer ({tau} : Set (PGammaL2 K)) := hx.1
    have hxpsl : x ∈ pGammaL2PSLRange K := hx.2
    have hxrange : x ∈ f.range := ad.pslRange_le hxpsl
    rcases MonoidHom.mem_range.mp hxrange with ⟨m, rfl⟩
    have hcomm : f m * f tM = f tM * f m := by
      rw [Subgroup.mem_centralizer_iff] at hxcent
      have hz : f tM ∈ ({tau} : Set (PGammaL2 K)) := by simpa [tau]
      exact (hxcent (f tM) hz).symm
    let j : d.E := ⟨(m : G) * (c.t : G) * (m : G)⁻¹,
      d.E_normal.2 (m : G) m.2 (c.t : G) (d.t_mem_E)⟩
    have hjt_ker : (j * tE⁻¹ : d.E) ∈ kerE := by
      rw [Subgroup.mem_comap]
      rw [MonoidHom.mem_ker]
      change f ((m : w.M) * tM * (m : w.M)⁻¹ * tM⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [hcomm]
      group
    have hnorm : kerE.Normal :=
      Subgroup.normal_comap iEM
    have hKodd : Odd (Nat.card kerE) := by
      have hle : kerE.map iEM ≤ f.ker := by
        intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact Subgroup.mem_comap.mp hy
      have h₁ : Nat.card kerE = Nat.card (kerE.map iEM) := by
        exact (Subgroup.card_map_of_injective
          ((MonoidHom.injective_codRestrict d.E.subtype w.M
            (fun x => d.E_component.1 x.2)).mpr d.E.subtype_injective)).symm
      have h₂ : Nat.card (kerE.map iEM) ∣ Nat.card f.ker :=
        Subgroup.card_dvd_of_le hle
      have hdvd : Nat.card kerE ∣ Nat.card f.ker := by
        rwa [← h₁] at h₂
      exact Odd.of_dvd_nat ad.ker_odd hdvd
    have hqE : IsQuasisimple (↥d.E) := d.E_component.2.2
    have hZE : kerE ≤ Subgroup.center (↥d.E) := by
      rcases normal_subgroup_le_center_or_eq_top hqE kerE hnorm with hc | htop
      · exact hc
      · exfalso
        have hEkle : d.E ≤ f.ker.map w.M.subtype := by
          intro x hx
          have hxkerE : (⟨x, hx⟩ : d.E) ∈ kerE := by
            rw [htop]
            exact Subgroup.mem_top _
          have hxker : (⟨x, d.E_component.1 hx⟩ : ↥w.M) ∈ f.ker :=
            Subgroup.mem_comap.mp hxkerE
          show ∃ y ∈ f.ker, w.M.subtype y = x
          exact ⟨⟨x, d.E_component.1 hx⟩, hxker, rfl⟩
        have hdvdE : Nat.card (↥d.E) ∣ Nat.card f.ker := by
          have h₁ : Nat.card (↥d.E) ∣ Nat.card (f.ker.map w.M.subtype) :=
            Subgroup.card_dvd_of_le hEkle
          have h₂ : Nat.card (f.ker.map w.M.subtype) = Nat.card f.ker := by
            exact (Subgroup.card_map_of_injective w.M.subtype_injective)
          rwa [h₂] at h₁
        have hEcard2 : 2 ∣ Nat.card (↥d.E) := by
          have hord2 : orderOf (tE : d.E) = 2 := by
            apply orderOf_eq_prime (p := 2)
            · change (tE : d.E) ^ 2 = 1
              apply Subtype.ext
              exact c.t_involution.2
            · exact fun h => c.t_involution.1 (by simpa [tE] using congrArg Subtype.val h)
          have hdvd : orderOf (tE : d.E) ∣ Nat.card (⊤ : Subgroup (↥d.E)) := by
            exact Subgroup.orderOf_dvd_natCard (⊤ : Subgroup (↥d.E)) (by trivial)
          have hdvd' : orderOf (tE : d.E) ∣ Nat.card (↥d.E) := by
            simpa using hdvd
          rwa [hord2] at hdvd'
        exact ad.ker_odd.not_two_dvd_nat (hEcard2.trans hdvdE)
    have hjtz : (j * tE⁻¹ : d.E) ∈ Subgroup.center (↥d.E) := hZE hjt_ker
    have hjtodd : Odd (orderOf (j * tE⁻¹ : d.E)) := by
      have hdvd : orderOf (j * tE⁻¹ : d.E) ∣ Nat.card kerE := by
        exact Subgroup.orderOf_dvd_natCard kerE hjt_ker
      exact Odd.of_dvd_nat hKodd hdvd
    have hj2 : (j : d.E) ^ 2 = 1 := by
      apply Subtype.ext
      change (j : G) ^ 2 = 1
      rw [show (j : G) = (m : G) * c.t * (m : G)⁻¹ by rfl]
      calc
        ((m : G) * c.t * (m : G)⁻¹) ^ 2 = (m : G) * (c.t * c.t) * (m : G)⁻¹ := by
          rw [pow_two]
          group
        _ = (m : G) * 1 * (m : G)⁻¹ := by rw [← pow_two, c.t_involution.2]
        _ = 1 := by group
    have ht2 : (tE⁻¹ : d.E) ^ 2 = 1 := by
      apply Subtype.ext
      change (c.t⁻¹) ^ 2 = (1 : G)
      rw [pow_two]
      calc
        c.t⁻¹ * c.t⁻¹ = (c.t * c.t)⁻¹ := by group
        _ = 1 := by rw [← pow_two, c.t_involution.2]; simp
        _ = 1 := by simp
    have hjtsq : (j * tE⁻¹ : d.E) ^ 2 = 1 := by
      have hsw : Commute (j : d.E) (tE⁻¹ : d.E) := by
        rw [Commute, SemiconjBy]
        have hc := (Subgroup.mem_center_iff.mp hjtz) (tE⁻¹ : d.E)
        apply mul_right_cancel (a := (j * tE⁻¹ : d.E))
          (c := (tE⁻¹ * j : d.E)) (b := (tE⁻¹ : d.E))
        simpa [mul_assoc] using hc.symm
      rw [pow_two]
      calc
        (j * tE⁻¹ : d.E) * (j * tE⁻¹ : d.E)
            = (j : d.E) * (tE⁻¹ * j : d.E) * tE⁻¹ := by group
        _ = (j : d.E) * (j * tE⁻¹ : d.E) * tE⁻¹ := by rw [hsw.eq]
        _ = (j : d.E) * (j : d.E) * (tE⁻¹ * tE⁻¹ : d.E) := by group
        _ = (tE⁻¹ * tE⁻¹ : d.E) := by
          rw [← pow_two, hj2]
          group
        _ = 1 := by
          rw [← pow_two, ht2]
    have hjt1 : j * tE⁻¹ = 1 := by
      have hdvd2 : orderOf (j * tE⁻¹ : d.E) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]
        simpa [pow_two] using hjtsq
      have hord1 : orderOf (j * tE⁻¹ : d.E) = 1 := by
        rcases hjtodd with ⟨k, hk⟩
        rw [hk] at hdvd2
        have hle : 2 * k + 1 ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2) hdvd2
        have hk0 : k = 0 := by omega
        rw [hk, hk0]
        norm_num
      exact (orderOf_eq_one_iff).mp hord1
    have hj : j = tE := by
      have h1 : j = (tE⁻¹)⁻¹ := (mul_eq_one_iff_eq_inv.mp hjt1)
      simpa using h1
    have hmC : m ∈ C := by
      rw [Subgroup.mem_comap]
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz1 : z = c.t := by simpa using hz
      rw [hz1]
      have hjval : (m : G) * c.t * (m : G)⁻¹ = c.t := by
        have := congrArg (fun x : d.E => (x : G)) hj
        simpa [j, tE, mul_assoc] using this
      have hctm : c.t * (m : G) = (m : G) * c.t := by
        calc
          c.t * (m : G) = (m : G) * c.t * (m : G)⁻¹ * (m : G) := by rw [hjval]
          _ = (m : G) * c.t := by group
      exact hctm
    change f m ∈ C.map f
    rw [Subgroup.mem_map]
    exact ⟨m, hmC, rfl⟩
  dsimp
  exact ⟨htauL, hAcent, hAcont⟩

end CFSG.GorensteinWalter
