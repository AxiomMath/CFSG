module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatExport
public import CFSG.Quasithin.Background.A3Structure312Transport
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.A312J2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem exists_conj_member {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) {J : ℕ} {Y : ℕ → Subgroup Γ}
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j) (K : Subgroup Γ)
    (hK : Nat.card S ∣ Nat.card K) :
    ∃ (g : Γ) (j : ℕ), j ≤ J ∧ K.map (MulAut.conj g).toMonoidHom = memberOrTop J Y j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp₀, hi₀⟩ := K1.isSylowTwoOf_top_iff.mp hS
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp₀
  have h2k : 2 ^ k ∣ Nat.card K := hk ▸ hK
  obtain ⟨R, hR⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 2 h2k
  let T : Subgroup Γ := R.map K.subtype
  have hTcard : Nat.card T = 2 ^ k := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hR]
  have hTp : IsPGroup 2 T := IsPGroup.of_card hTcard
  have hTi : ¬ 2 ∣ T.index := by
    have h1 := Subgroup.card_mul_index S
    have h2 := Subgroup.card_mul_index T
    rw [hk] at h1
    rw [hTcard] at h2
    have : T.index = S.index := Nat.eq_of_mul_eq_mul_left (by positivity) (h2.trans h1.symm)
    rw [this]
    exact hi₀
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hTp.toSylow hTi) (hp₀.toSylow hi₀)
  have hST : S = T.map (MulAut.conj g).toMonoidHom := by
    have := congrArg (fun P : Sylow 2 Γ => (P : Subgroup Γ)) hg
    exact this.symm
  have hTK : T ≤ K := by
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  have hSK : S ≤ K.map (MulAut.conj g).toMonoidHom := by
    rw [hST]
    exact Subgroup.map_mono hTK
  obtain ⟨j, hj, hZ⟩ := hall _ hSK
  exact ⟨g, j, hj, hZ⟩

theorem exists_equiv_member {Γ H : Type} [Group Γ] [Finite Γ] [Group H] {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) {J : ℕ} {Y : ℕ → Subgroup Γ}
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j) (K : Subgroup Γ)
    (hK : Nat.card S ∣ Nat.card K) (e : ↥K ≃* H) :
    ∃ j ≤ J, Nonempty (↥(memberOrTop J Y j) ≃* H) := by
  obtain ⟨g, j, hj, hZ⟩ := exists_conj_member hS hall K hK
  refine ⟨j, hj, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr hZ.symm).trans
    ((K.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans e)

theorem exists_member_ext {Γ P A : Type} [Group Γ] [Finite Γ] [Group P] [Group A]
    (ψ : Γ ≃* P) {S : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) {J : ℕ} {Y : ℕ → Subgroup Γ}
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j) (H : Subgroup P)
    (eH : ↥H ≃* A) (hK : Nat.card S ∣ Nat.card A)
    {PV PY : ∀ (V : Type) [Group V], Prop}
    (hV : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PV V → PV W)
    (hY : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PY V → PY W)
    (hext : IsExt A PV PY) (hperf : Group.IsPerfect A) :
    ∃ j ≤ J, Nat.card (memberOrTop J Y j) = Nat.card A ∧ IsExt ↥(memberOrTop J Y j) PV PY ∧
      ⁅memberOrTop J Y j, memberOrTop J Y j⁆ = memberOrTop J Y j := by
  let e : ↥(H.comap ψ.toMonoidHom) ≃* A :=
    ((MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm ψ H)).trans
      (H.equivMapOfInjective ψ.symm.toMonoidHom ψ.symm.injective).symm).trans eH
  obtain ⟨j, hj, ⟨eY⟩⟩ := exists_equiv_member hS hall _
    (by rw [Nat.card_congr e.toEquiv]; exact hK) e
  refine ⟨j, hj, Nat.card_congr eY.toEquiv, A312.isExt_of_mulEquiv hV hY eY.symm hext, ?_⟩
  have : Group.IsPerfect ↥(memberOrTop J Y j) :=
    Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
  exact Subgroup.isPerfect_iff.mp this

end CFSG.Quasithin.A312J2
