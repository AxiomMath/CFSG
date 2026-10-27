module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagLin
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix

section Toral

private theorem exists_compl_zpowers_of_elemAbelian {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {z : G} (hz : z ∈ Bs) :
    ∃ E : Subgroup G, E ≤ Bs ∧ IsElemAbelian p E ∧
      Subgroup.zpowers z ⊓ E = ⊥ ∧ Subgroup.zpowers z ⊔ E = Bs ∧
      (∀ b ∈ Bs, ∃ y ∈ Subgroup.zpowers z, ∃ e ∈ E, y * e = b) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsElementaryAbelian p ↥Bs :=
    { toIsMulCommutative := hBs.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x => Subtype.ext (hBs.2 x x.2)) }
  obtain ⟨C, hC⟩ :=
    IsElementaryAbelian.exists_isCompl p ↥Bs (Subgroup.zpowers (⟨z, hz⟩ : ↥Bs))
  haveI : IsElementaryAbelian p C :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        apply Subtype.ext
        have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p p ↥Bs) (x : ↥Bs)
        simpa using this) }
  let E : Subgroup G := C.map Bs.subtype
  haveI hEinst : IsElementaryAbelian p E :=
    IsElementaryAbelian.map_subtype (p := p) (K := Bs) (H := C)
  have hmap : (Subgroup.zpowers (⟨z, hz⟩ : ↥Bs)).map Bs.subtype = Subgroup.zpowers z :=
    MonoidHom.map_zpowers Bs.subtype ⟨z, hz⟩
  refine ⟨E, Subgroup.map_subtype_le C, ?_, ?_, ?_, ?_⟩
  · exact ⟨inferInstance, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxZ, hxE⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hxE
    have hcZ : c ∈ Subgroup.zpowers (⟨z, hz⟩ : ↥Bs) := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxZ
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have h1 : c ∈ Subgroup.zpowers (⟨z, hz⟩ : ↥Bs) ⊓ C :=
      Subgroup.mem_inf.mpr ⟨hcZ, hc⟩
    rw [hC.disjoint.eq_bot, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  · have hsup := congrArg (Subgroup.map Bs.subtype) hC.sup_eq_top
    rw [Subgroup.map_sup, hmap, Subgroup.map_top, Subgroup.range_subtype] at hsup
    exact hsup
  · haveI : IsMulCommutative ↥Bs := hBs.1
    let _ : CommGroup ↥Bs :=
      { (inferInstance : Group ↥Bs) with mul_comm := fun a b => mul_comm' a b }
    intro b hb
    have h1 : (⟨b, hb⟩ : ↥Bs) ∈ Subgroup.zpowers (⟨z, hz⟩ : ↥Bs) ⊔ C := by
      rw [hC.sup_eq_top]
      trivial
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (Subgroup.mem_sup (s := Subgroup.zpowers (⟨z, hz⟩ : ↥Bs)) (t := C)).mp h1
    exact ⟨(x : G), hmap ▸ Subgroup.mem_map_of_mem Bs.subtype hx, (y : G),
      Subgroup.mem_map_of_mem Bs.subtype hy, congrArg Subtype.val hxy⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_actsDiag_of_bstar {p n f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) {Bs M : Subgroup G} (hBs : IsElemAbelian p Bs) {z : G}
    (hz : Bs ⊓ Subgroup.centralizer (M : Set G) = Subgroup.zpowers z)
    (hbig : p ^ ((n + 1) / p + 3) ≤ Nat.card Bs)
    {φ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)))
    (hrange : φ.range = M)
    (hBA : ∀ b ∈ Bs, ∃ A : GL (Fin (n + 1)) (GaloisField 2 f),
      (b, A) ∈ LinFusion.ggInducedPairs φ) :
    ∃ φ' : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ'.range = M ∧
      φ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      ∀ b ∈ Bs, GGActsDiag φ' b := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpf
  have hz_mem : z ∈ Bs ⊓ Subgroup.centralizer (M : Set G) := by
    rw [hz]; exact Subgroup.mem_zpowers z
  obtain ⟨hzBs, hzC⟩ := Subgroup.mem_inf.mp hz_mem
  have hzpow : z ^ p = 1 := hBs.2 z hzBs
  obtain ⟨E, hEBs, hE, hEdisj, hEsup, hEdecomp⟩ :=
    exists_compl_zpowers_of_elemAbelian hp hBs hzBs
  have hzcard : Nat.card (Subgroup.zpowers z) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hzpow)
  have hcard_le : Nat.card Bs ≤ p * Nat.card E := by
    let f : Subgroup.zpowers z × E → ↥Bs := fun x =>
      ⟨(x.1 : G) * (x.2 : G), hEsup ▸ Subgroup.mul_mem_sup x.1.2 x.2.2⟩
    have hsurj : Function.Surjective f := by
      rintro ⟨b, hb⟩
      obtain ⟨y, hy, e, he, hye⟩ := hEdecomp b hb
      exact ⟨(⟨y, hy⟩, ⟨e, he⟩), Subtype.ext hye⟩
    calc Nat.card Bs ≤ Nat.card (Subgroup.zpowers z × E) :=
          Nat.card_le_card_of_surjective f hsurj
      _ = Nat.card (Subgroup.zpowers z) * Nat.card E := Nat.card_prod _ _
      _ ≤ p * Nat.card E := Nat.mul_le_mul_right _ hzcard
  have hbig' : p ^ ((n + 1) / p + 1) < Nat.card E := by
    have h2 : p ^ ((n + 1) / p + 2) ≤ Nat.card E := by
      have hpow : p ^ ((n + 1) / p + 3) = p * p ^ ((n + 1) / p + 2) := by
        rw [show (n + 1) / p + 3 = ((n + 1) / p + 2) + 1 by omega, pow_succ]
        ring
      have h := hbig.trans hcard_le
      rw [hpow] at h
      exact Nat.le_of_mul_le_mul_left h hp.pos
    calc p ^ ((n + 1) / p + 1) < p ^ ((n + 1) / p + 2) :=
          Nat.pow_lt_pow_right hp.one_lt (by omega)
      _ ≤ Nat.card E := h2
  have hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ LinFusion.ggInducedPairs φ := fun e he => hBA e (hEBs he)
  have hEC : E ⊓ Subgroup.centralizer (φ.range : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgE, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgCM : g ∈ Subgroup.centralizer (M : Set G) := by rwa [← hrange]
    have hgZ : g ∈ Subgroup.zpowers z := by
      have h1 : g ∈ Bs ⊓ Subgroup.centralizer (M : Set G) :=
        Subgroup.mem_inf.mpr ⟨hEBs hgE, hgCM⟩
      rwa [hz] at h1
    have h2 : g ∈ Subgroup.zpowers z ⊓ E := Subgroup.mem_inf.mpr ⟨hgZ, hgE⟩
    rwa [hEdisj, Subgroup.mem_bot] at h2
  obtain ⟨P, hP⟩ := LinTorus.exists_le_ggFrameTorus hp hp2 hpF hker hE hbig' hEA hEC
  let φ' : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G :=
    φ.comp (InnerDiagA.conjSL P⁻¹)
  have hrange' : φ'.range = M := by
    change (φ.comp (InnerDiagA.conjSL P⁻¹)).range = M
    rw [LinTorus.range_comp_conjSL, hrange]
  have hker' : φ'.ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) := by
    change (φ.comp (InnerDiagA.conjSL P⁻¹)).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f))
    exact LinTorus.ker_comp_conjSL_le hker P⁻¹
  have hzv : GGActsVec φ' z 1 := by
    apply GGActsVec.one_of_commute
    intro s
    have hzC' : z ∈ Subgroup.centralizer (φ'.range : Set G) := by rw [hrange']; exact hzC
    have hs : φ' s ∈ φ'.range := MonoidHom.mem_range.mpr ⟨s, rfl⟩
    exact ((Subgroup.mem_centralizer_iff.mp hzC') (φ' s) hs).symm
  have hEv : ∀ e ∈ E, GGActsDiag φ' e := by
    intro e he
    obtain ⟨d, hd⟩ := hP he
    refine ⟨d, ?_⟩
    refine (ggActsVec_iff_mem_ggInducedPairs (φ := φ') (g := e) (h := d)).mpr ?_
    change (e, InnerDiagA.diagGL d) ∈
      LinFusion.ggInducedPairs (φ.comp (InnerDiagA.conjSL P⁻¹))
    exact LinTorus.mem_ggInducedPairs_frame hd
  let D : Subgroup G :=
    { carrier := {g | GGActsDiag φ' g}
      one_mem' := ⟨1, GGActsVec.one_of_commute (fun s => by group)⟩
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨ca, hca⟩ := ha
        obtain ⟨cb, hcb⟩ := hb
        exact ⟨ca * cb, GGActsVec.mul hca hcb⟩
      inv_mem' := fun {a} ha => by
        obtain ⟨ca, hca⟩ := ha
        exact ⟨ca⁻¹, GGActsVec.inv hca⟩ }
  have hBD : Bs ≤ D := by
    rw [← hEsup]
    exact sup_le (Subgroup.zpowers_le.mpr ⟨1, hzv⟩) hEv
  exact ⟨φ', hrange', hker', fun b hb => hBD hb⟩

end Toral

end CFSG.StandardType

end
