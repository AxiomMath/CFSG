module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoPairs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.RankThree.PartOne.CTP.StrongPTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem normalizer_AA_le {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p) :
    Subgroup.normalizer (t.d.AA : Set G) ≤ c.S.M := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommAA : ∀ a ∈ t.d.AA, ∀ b ∈ t.d.AA, a * b = b * a :=
    fun a ha b hb =>
      congrArg Subtype.val ((t.d.isElemAbelian_AA.1).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBcard : Nat.card (t.d.A 0 ⊔ t.d.A 1 : Subgroup G) = 9 := by
    rw [t.d.card_A_sup_A (by decide)]
    norm_num
  have hBAA : (t.d.A 0 ⊔ t.d.A 1 : Subgroup G) ≤ t.d.AA := by
    rw [t.d.AA_def]
    exact le_sup_left
  intro g hg
  have hAg : t.d.AA.map (MulAut.conj g).toMonoidHom = t.d.AA :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hBgAA : (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom ≤ t.d.AA := by
    calc (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom
        ≤ t.d.AA.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hBAA
      _ = t.d.AA := hAg
  have hBgcard : Nat.card ((t.d.A 0 ⊔ t.d.A 1).map
      (MulAut.conj g).toMonoidHom : Subgroup G) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hBcard]
  have hcomm : ∀ x ∈ (t.d.A 0 ⊔ t.d.A 1 : Subgroup G),
      ∀ y ∈ ((t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom : Subgroup G),
      x * y = y * x :=
    fun x hx y hy => hcommAA x (hBAA hx) y (hBgAA hy)
  have hcard_mul : Nat.card ((t.d.A 0 ⊔ t.d.A 1) ⊔
      (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom : Subgroup G) *
      Nat.card ((t.d.A 0 ⊔ t.d.A 1) ⊓
      (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom : Subgroup G) = 9 * 9 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (t.d.A 0 ⊔ t.d.A 1) ((t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom) hcomm).1
    rwa [hBcard, hBgcard] at h
  have hsup_le : Nat.card ((t.d.A 0 ⊔ t.d.A 1) ⊔
      (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 27 := by
    calc Nat.card ((t.d.A 0 ⊔ t.d.A 1) ⊔
          (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom : Subgroup G)
        ≤ Nat.card t.d.AA := Subgroup.card_le_of_le (sup_le hBAA hBgAA)
      _ = 27 := t.d.card_AA
  have hinf_ne_one : Nat.card ((t.d.A 0 ⊔ t.d.A 1) ⊓
      (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom : Subgroup G) ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hcard_mul
    omega
  haveI : Nonempty ↥((t.d.A 0 ⊔ t.d.A 1) ⊓
      (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom) := ⟨1⟩
  have hpos : 0 < Nat.card ((t.d.A 0 ⊔ t.d.A 1) ⊓
      (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom : Subgroup G) := Nat.card_pos
  haveI : Nontrivial ↥((t.d.A 0 ⊔ t.d.A 1) ⊓
      (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx1⟩ := exists_ne (1 : ↥((t.d.A 0 ⊔ t.d.A 1) ⊓
    (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom))
  let xg : G := (x : G)
  have hxmem : xg ∈ t.d.A 0 ⊔ t.d.A 1 := x.2.1
  have hxmem' : xg ∈ (t.d.A 0 ⊔ t.d.A 1).map (MulAut.conj g).toMonoidHom := x.2.2
  have hxne : xg ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨b, hbB, hbconj⟩ := Subgroup.mem_map.mp hxmem'
  have hbeq : g⁻¹ * xg * g = b := by
    rw [← hbconj]
    simp [MulAut.conj_apply, mul_assoc]
  let X : Subgroup G := Subgroup.zpowers (g⁻¹ * xg * g)
  have hX_le_B : X ≤ t.d.A 0 ⊔ t.d.A 1 := by
    change Subgroup.zpowers (g⁻¹ * xg * g) ≤ t.d.A 0 ⊔ t.d.A 1
    rw [hbeq]
    exact Subgroup.zpowers_le.mpr hbB
  have hX_ne : X ≠ ⊥ := by
    rw [show X = Subgroup.zpowers (g⁻¹ * xg * g) from rfl, Subgroup.zpowers_ne_bot]
    intro h
    apply hxne
    have hc := congrArg (MulAut.conj g) h
    simpa [MulAut.conj_apply, mul_assoc] using hc
  have hXg_eq : X.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers xg := by
    change (Subgroup.zpowers (g⁻¹ * xg * g)).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers xg
    rw [MonoidHom.map_zpowers]
    congr 1
    simp [MulAut.conj_apply, mul_assoc]
  have hXg_le_B : X.map (MulAut.conj g).toMonoidHom ≤ t.d.A 0 ⊔ t.d.A 1 := by
    rw [hXg_eq]
    exact Subgroup.zpowers_le.mpr hxmem
  have hN_le : Subgroup.normalizer (X : Set G) ≤ c.S.M :=
    hN.normalizer_le (i := 0) (j := 1) (by decide) hX_le_B hX_ne
  have hC_le : Subgroup.centralizer (X : Set G) ≤ c.S.M :=
    (Subgroup.centralizer_le_normalizer (X : Set G)).trans hN_le
  have hMcapB_dvd : p ∣ Nat.card (c.S.M ⊓ Subgroup.centralizer
      ((t.d.A 0 ⊔ t.d.A 1 : Subgroup G) : Set G) : Subgroup G) :=
    hN.dvd_card (i := 0) (j := 1) (by decide)
  have hMcapXg_dvd : p ∣ Nat.card (c.S.M ⊓ Subgroup.centralizer
      ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) : Subgroup G) := by
    refine hMcapB_dvd.trans (Subgroup.card_dvd_of_le ?_)
    exact inf_le_inf le_rfl (Subgroup.centralizer_le hXg_le_B)
  exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.mem_of_centralizer_le
    (hY := c.isStronglyPEmbedded_of_mem_sigma hp) (hX := hC_le) (hp := hMcapXg_dvd)

theorem normalizer_P_le {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p) :
    Subgroup.normalizer (t.P : Set G) ≤ c.S.M := by
  have hSP : t.d.S ≤ t.P := by
    rw [t.hdS]
    exact inf_le_left
  have hAAleP : t.d.AA ≤ t.P := t.d.AA_le_S.trans hSP
  intro n hn
  have hPn : t.P.map (MulAut.conj n).toMonoidHom = t.P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hAn : t.d.AA.map (MulAut.conj n).toMonoidHom = t.d.AA := by
    refine t.eq_AA_of_isElemAbelian ?_ ?_ ?_
    · calc t.d.AA.map (MulAut.conj n).toMonoidHom
          ≤ t.P.map (MulAut.conj n).toMonoidHom := Subgroup.map_mono hAAleP
        _ = t.P := hPn
    · exact CFSG.Open.IsElemAbelian.map t.d.isElemAbelian_AA (MulAut.conj n).toMonoidHom
    · rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, t.d.card_AA]
  exact normalizer_AA_le t hp hN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hAn)

theorem isSylowOf_top {p : ℕ} (hp : p ∈ c.sig) (hN : t.PairNormalizerLe p) :
    CFSG.ABGLocalTools.IsSylowOf 3 t.P ⊤ := by
  have hT : CFSG.ABGLocalTools.IsSylowOf 3 t.P (c.S.M ⊓ ⊤) := by
    simpa using t.hP
  have hNle : Subgroup.normalizer (t.P : Set G) ⊓ ⊤ ≤ c.S.M := by
    simpa using normalizer_P_le t hp hN
  exact CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le hT hNle

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
