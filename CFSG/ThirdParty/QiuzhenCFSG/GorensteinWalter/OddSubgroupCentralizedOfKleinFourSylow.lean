module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralReflectionCentralizerCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralRotationIndexTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeNormalIndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd subgroups in the Klein-four Sylow dihedral case

Suppose `M` is dihedral and contains a Klein-four subgroup `S`.  If the
ambient centralizer of an involution `t ∈ S` lies in `M`, and all ambient
involutions are conjugate, then every odd-order subgroup of `M` centralizes
`t`.  A rotation `t` lies in the cyclic rotation subgroup directly.  If `t`
is a reflection, its ambient centralizer has order at most four; conjugacy to
the central half-turn of `M` then forces `M` itself to have order four.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In a finite group with one involution conjugacy class, the distinguished
involution in a contained Klein four centralizes every odd-order subgroup of
a dihedral overgroup whose ambient centralizer it controls. -/
public theorem odd_subgroup_le_centralizer_of_klein_four_sylow_in_dihedral_subgroup
    {G : Type u} [Group G] [Finite G]
    (S M P : Subgroup G) {z : ℕ}
    (eS : S ≃* DihedralGroup 2)
    (eM : M ≃* DihedralGroup z)
    (hMcard : Nat.card M = 2 * z)
    (hSM : S ≤ M) (hPM : P ≤ M)
    (hPodd : Odd (Nat.card P))
    {t : G} (htS : t ∈ S) (ht : IsInvolution t)
    (hCM : Subgroup.centralizer ({t} : Set G) ≤ M)
    (hinvconj : ∀ x y : G, IsInvolution x → IsInvolution y →
      ∃ g : G, g * x * g⁻¹ = y) :
    P ≤ Subgroup.centralizer ({t} : Set G) := by
  classical
  have hScard : Nat.card S = 4 := by
    calc
      Nat.card S = Nat.card (DihedralGroup 2) :=
        Nat.card_congr eS.toEquiv
      _ = 4 := DihedralGroup.nat_card
  have hSdvdM : Nat.card S ∣ Nat.card M :=
    Subgroup.card_dvd_of_le hSM
  have hfour_dvd : 4 ∣ 2 * z := by
    rwa [hScard, hMcard] at hSdvdM
  have htwo_dvd_z : 2 ∣ z := by
    have h : 2 * 2 ∣ 2 * z := by
      norm_num at hfour_dvd ⊢
      exact hfour_dvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h
  rcases htwo_dvd_z with ⟨k, rfl⟩
  have hk : k ≠ 0 := by
    intro hk0
    subst k
    have hMpos : 0 < Nat.card M := Nat.card_pos
    rw [hMcard] at hMpos
    simp at hMpos
  let : NeZero k := ⟨hk⟩
  let RD : Subgroup (DihedralGroup (2 * k)) :=
    Subgroup.zpowers (DihedralGroup.r 1)
  let RM : Subgroup M := RD.comap eM.toMonoidHom
  have hRMindex : RM.index = 2 := by
    calc
      RM.index = RD.index :=
        Subgroup.index_comap_of_surjective RD eM.surjective
      _ = 2 := dihedral_rotation_index_two
  have hRMnormal : RM.Normal :=
    Subgroup.normal_of_index_eq_two hRMindex
  let PM : Subgroup M := P.subgroupOf M
  have hPModd : Odd (Nat.card PM) := by
    have hcard : Nat.card PM = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv
    rwa [hcard]
  have hPMleRM : PM ≤ RM :=
    odd_card_subgroup_le_normal_index_two
      RM PM hRMnormal hRMindex hPModd
  let tM : M := ⟨t, hSM htS⟩
  have hcentral_of_tRM (htRM : tM ∈ RM) :
      P ≤ Subgroup.centralizer ({t} : Set G) := by
    intro x hxP
    let xM : M := ⟨x, hPM hxP⟩
    have hxPM : xM ∈ PM := Subgroup.mem_subgroupOf.mpr hxP
    have hxRM : xM ∈ RM := hPMleRM hxPM
    have htRD : eM tM ∈ RD := htRM
    have hxRD : eM xM ∈ RD := hxRM
    let tR : RD := ⟨eM tM, htRD⟩
    let xR : RD := ⟨eM xM, hxRD⟩
    let : IsCyclic RD := by
      dsimp [RD]
      infer_instance
    have hcommR : tR * xR = xR * tR := mul_comm' tR xR
    have hcommM : (tM : M) * xM = xM * tM := by
      apply eM.injective
      simpa [tR, xR] using congrArg Subtype.val hcommR
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyt : y = t := Set.mem_singleton_iff.mp hy
    subst y
    exact congrArg Subtype.val hcommM
  rcases htd : eM tM with i | i
  · apply hcentral_of_tRM
    change eM tM ∈ RD
    rw [htd]
    exact r_mem_zpowers_r_one i
  · let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
    let CM : Subgroup M := C.subgroupOf M
    let CD : Subgroup (DihedralGroup (2 * k)) :=
      CM.map eM.toMonoidHom
    have hCDle : CD ≤ Subgroup.centralizer
        ({DihedralGroup.sr i} : Set (DihedralGroup (2 * k))) := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hxCM, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwri : w = DihedralGroup.sr i :=
        Set.mem_singleton_iff.mp hw
      subst w
      have hxC : (x : G) ∈ C := Subgroup.mem_subgroupOf.mp hxCM
      have hcommG : t * (x : G) = (x : G) * t :=
        (Subgroup.mem_centralizer_iff.mp hxC) t (by simp)
      have hcommM : tM * x = x * tM := Subtype.ext hcommG
      have hecomm := congrArg eM hcommM
      simpa [htd] using hecomm
    have hCDcard : Nat.card CD = Nat.card C := by
      calc
        Nat.card CD = Nat.card CM := by
          symm
          exact Nat.card_congr
            (CM.equivMapOfInjective
              eM.toMonoidHom eM.injective).toEquiv
        _ = Nat.card C :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv
    have hCDcard_le : Nat.card CD ≤ 4 := by
      have hinj : Function.Injective (fun x : CD =>
          (⟨x, hCDle x.property⟩ :
            Subgroup.centralizer
              ({DihedralGroup.sr i} : Set (DihedralGroup (2 * k))))) := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg
          (fun q : Subgroup.centralizer
            ({DihedralGroup.sr i} : Set (DihedralGroup (2 * k))) =>
              (q : DihedralGroup (2 * k))) hxy
      calc
        Nat.card CD ≤ Nat.card (Subgroup.centralizer
            ({DihedralGroup.sr i} : Set (DihedralGroup (2 * k)))) :=
          Nat.card_le_card_of_injective _ hinj
        _ ≤ 4 :=
          card_centralizer_reflection_dihedral_even_le_four i
    have hCcard_le : Nat.card C ≤ 4 := by
      rwa [hCDcard] at hCDcard_le
    let uD : DihedralGroup (2 * k) :=
      DihedralGroup.r (k : ZMod (2 * k))
    have htwo_k : (k : ZMod (2 * k)) + k = 0 := by
      calc
        (k : ZMod (2 * k)) + k =
            ((2 * k : ℕ) : ZMod (2 * k)) := by
          push_cast
          ring
        _ = 0 := ZMod.natCast_self (2 * k)
    have hneg_k : -(k : ZMod (2 * k)) = k :=
      (neg_eq_iff_add_eq_zero).mpr
        (by simpa [add_comm] using htwo_k)
    have huDcenter : uD ∈
        Subgroup.center (DihedralGroup (2 * k)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      rcases y with j | j
      · simp [uD, add_comm]
      · simp [uD, sub_eq_add_neg, hneg_k]
    have huDpow : uD ^ 2 = 1 := by
      simp [uD, pow_two, htwo_k]
    have huDne : uD ≠ 1 := by
      intro huone
      have hkcast : (k : ZMod (2 * k)) = 0 := by
        simpa [uD, DihedralGroup.one_def] using
          DihedralGroup.r.inj huone
      have hkdvd : 2 * k ∣ k :=
        (ZMod.natCast_eq_zero_iff k (2 * k)).mp hkcast
      have hle : 2 * k ≤ k :=
        Nat.le_of_dvd (NeZero.pos k) hkdvd
      omega
    let uM : M := eM.symm uD
    let u : G := uM
    have huMcenter : uM ∈ Subgroup.center M :=
      MulEquivClass.apply_mem_center eM.symm huDcenter
    have hu : IsInvolution u := by
      have huMpow : uM ^ 2 = 1 := by
        apply eM.injective
        simpa [uM] using huDpow
      have huMne : uM ≠ 1 := by
        intro huone
        apply huDne
        simpa [uM] using congrArg eM huone
      constructor
      · intro huone
        apply huMne
        apply Subtype.ext
        simpa [u] using huone
      · simpa [u] using congrArg Subtype.val huMpow
    obtain ⟨g, hgtu⟩ := hinvconj t u ht hu
    let Cu : Subgroup G := Subgroup.centralizer ({u} : Set G)
    let eC : C ≃ Cu := by
      let forward : C → Cu := fun x => ⟨g * (x : G) * g⁻¹, by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyu : y = u := Set.mem_singleton_iff.mp hy
        subst y
        have hxcomm : t * (x : G) = (x : G) * t :=
          (Subgroup.mem_centralizer_iff.mp x.property) t (by simp)
        rw [← hgtu]
        calc
          (g * t * g⁻¹) * (g * (x : G) * g⁻¹) =
              g * (t * (x : G)) * g⁻¹ := by group
          _ = g * ((x : G) * t) * g⁻¹ := by rw [hxcomm]
          _ = (g * (x : G) * g⁻¹) * (g * t * g⁻¹) := by group⟩
      let backward : Cu → C := fun x => ⟨g⁻¹ * (x : G) * g, by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyt : y = t := Set.mem_singleton_iff.mp hy
        subst y
        have hxcomm : u * (x : G) = (x : G) * u :=
          (Subgroup.mem_centralizer_iff.mp x.property) u (by simp)
        have htback : g⁻¹ * u * g = t := by
          rw [← hgtu]
          group
        rw [← htback]
        calc
          (g⁻¹ * u * g) * (g⁻¹ * (x : G) * g) =
              g⁻¹ * (u * (x : G)) * g := by group
          _ = g⁻¹ * ((x : G) * u) * g := by rw [hxcomm]
          _ = (g⁻¹ * (x : G) * g) * (g⁻¹ * u * g) := by group⟩
      exact
        { toFun := forward
          invFun := backward
          left_inv := by
            intro x
            apply Subtype.ext
            dsimp [forward, backward]
            group
          right_inv := by
            intro x
            apply Subtype.ext
            dsimp [forward, backward]
            group }
    have hCucard_le : Nat.card Cu ≤ 4 := by
      rw [← Nat.card_congr eC]
      exact hCcard_le
    have hMleCu : M ≤ Cu := by
      intro x hxM
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyu : y = u := Set.mem_singleton_iff.mp hy
      subst y
      let xM : M := ⟨x, hxM⟩
      have hcomm := Subgroup.mem_center_iff.mp huMcenter xM
      exact (congrArg Subtype.val hcomm).symm
    have hMcard_le : Nat.card M ≤ 4 := by
      have hinj : Function.Injective (fun x : M =>
          (⟨x, hMleCu x.property⟩ : Cu)) := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun q : Cu => (q : G)) hxy
      exact (Nat.card_le_card_of_injective _ hinj).trans hCucard_le
    have hPcard_le : Nat.card P ≤ 4 :=
      (Nat.le_of_dvd Nat.card_pos
        (Subgroup.card_dvd_of_le hPM)).trans hMcard_le
    have hPcard_dvd_four : Nat.card P ∣ 4 :=
      (Subgroup.card_dvd_of_le hPM).trans (by
        have hMcard_eq : Nat.card M = 4 := by
          apply le_antisymm hMcard_le
          have hfour_dvd_M : 4 ∣ Nat.card M := by
            rwa [hScard] at hSdvdM
          exact Nat.le_of_dvd Nat.card_pos hfour_dvd_M
        rw [hMcard_eq])
    have hPcard_one : Nat.card P = 1 := by
      interval_cases hc : Nat.card P
      · have hPpos : 0 < Nat.card P := Nat.card_pos
        omega
      · rfl
      · norm_num at hPodd
      · norm_num at hPcard_dvd_four
      · norm_num at hPodd
    have hPbot : P = ⊥ :=
      Subgroup.eq_bot_of_card_eq (H := P) hPcard_one
    intro x hxP
    have hxone : x = 1 := by
      rw [hPbot] at hxP
      exact Subgroup.mem_bot.mp hxP
    rw [Subgroup.mem_centralizer_iff]
    intro y _hy
    simp [hxone]

end CFSG.GorensteinWalter
