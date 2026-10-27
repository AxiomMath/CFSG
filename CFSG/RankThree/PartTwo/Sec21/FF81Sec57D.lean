module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57B
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec57KDefs
import CFSG.RankThree.PartTwo.Sec21.FF81Sec52C
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CSyl
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate7233Base
public import Certificates.Certificate899101

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open P51 (V e)

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

theorem S57.card_sup_le {N H : Subgroup G} (hLE : H ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card ↥(N ⊔ H) ≤ Nat.card N * Nat.card H := by
  have h := Set.natCard_mul_le (s := (N : Set G)) (t := (H : Set G))
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left N H hLE] at h
  exact h

theorem S57.conj_comm {g x y : G} (h : x * y = y * x) :
    g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹) := by
  calc g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [h]
    _ = g * y * g⁻¹ * (g * x * g⁻¹) := by group

theorem S57.card_J {J : Subgroup G} (e : ↥J ≃* Equiv.Perm (Fin 6)) : Nat.card J = 720 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

def S57.f3 (v : V) : V := ![v 0, v 1, v 2, -v 3]

def S57.fs (v : V) : V := ![v 0, v 1, -v 3, -v 2]

section T3

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.exists_t₃ : ∃ t : G, ∀ v, t * h5.ε v * t⁻¹ = h5.ε (S57.f3 v) := by
  obtain ⟨-, -, -, ⟨n, -, h0, h1, h2, h3⟩, -, ⟨c, -, c0, c1, c2, c3⟩⟩ := h5.basis.mono
  have inv : ∀ {x y : G}, c * x * c⁻¹ = y → c⁻¹ * y * c = x := fun h => by rw [← h]; group
  refine ⟨c⁻¹ * n * c, fun v => ?_⟩
  have e0 : c⁻¹ * n * c * b * (c⁻¹ * n * c)⁻¹ = h5.ε (e 0) := by
    calc _ = c⁻¹ * (n * (c * b * c⁻¹) * n⁻¹) * c := by group
      _ = b := by rw [c0, h0, inv c0]
      _ = _ := h5.ε_e0.symm
  have e1 : c⁻¹ * n * c * b₁ * (c⁻¹ * n * c)⁻¹ = h5.ε (e 1) := by
    calc _ = c⁻¹ * (n * (c * b₁ * c⁻¹) * n⁻¹) * c := by group
      _ = b₁ := by rw [c1, h2, inv c1]
      _ = _ := h5.ε_e1.symm
  have e2 : c⁻¹ * n * c * b₂ * (c⁻¹ * n * c)⁻¹ = h5.ε (e 2) := by
    calc _ = c⁻¹ * (n * (c * b₂ * c⁻¹) * n⁻¹) * c := by group
      _ = b₂ := by rw [c2, h3, inv c2]
      _ = _ := h5.ε_e2.symm
  have e3 : c⁻¹ * n * c * b₃ * (c⁻¹ * n * c)⁻¹ = h5.ε (-e 3) := by
    calc _ = c⁻¹ * (n * (c * b₃ * c⁻¹) * n⁻¹) * c := by group
      _ = (c⁻¹ * b₁ * c)⁻¹ := by rw [c3, h1]; group
      _ = b₃⁻¹ := by rw [inv c3]
      _ = _ := by rw [h5.ε_neg, h5.ε_e3]
  rw [ε4_conj h5.hE h5.hcl ![e 0, e 1, e 2, -e 3] e0 e1 e2 e3]
  congr 1
  ext j; fin_cases j <;> simp [S57.f3, e, Pi.single_apply]

variable {t : G} (ht : ∀ v, t * h5.ε v * t⁻¹ = h5.ε (S57.f3 v))
include ht

theorem FF81Sec5.t₃_inv_ε (v : V) : t⁻¹ * h5.ε v * t = h5.ε (S57.f3 v) := by
  have h := ht (S57.f3 v)
  have hv : S57.f3 (S57.f3 v) = v := by ext j; fin_cases j <;> simp [S57.f3]
  rw [hv] at h
  rw [← h]; group

theorem FF81Sec5.sstar_ε (v : V) :
    t * s₀ * t⁻¹ * h5.ε v * (t * s₀ * t⁻¹)⁻¹ = h5.ε (S57.fs v) := by
  have h : t * s₀ * t⁻¹ * h5.ε v * (t * s₀ * t⁻¹)⁻¹ =
      t * (s₀ * (t⁻¹ * h5.ε v * t) * s₀⁻¹) * t⁻¹ := by group
  rw [h, h5.t₃_inv_ε ht, h5.s₀_ε, ht]
  congr 1

theorem FF81Sec5.sstar_β : t * s₀ * t⁻¹ * β' b₂ b₃ = β' b₂ b₃ * (t * s₀ * t⁻¹) := by
  have h := h5.sstar_ε ht ![0, 0, 1, 2]
  have hv : S57.fs ![0, 0, 1, 2] = ![0, 0, 1, 2] := by decide
  rw [hv, h5.ε_β] at h
  calc t * s₀ * t⁻¹ * β' b₂ b₃
      = t * s₀ * t⁻¹ * β' b₂ b₃ * (t * s₀ * t⁻¹)⁻¹ * (t * s₀ * t⁻¹) := by group
    _ = β' b₂ b₃ * (t * s₀ * t⁻¹) := by rw [h]

theorem FF81Sec5.orderOf_sstar : orderOf (t * s₀ * t⁻¹) = 2 := by
  change orderOf ((MulAut.conj t).toMonoidHom s₀) = 2
  exact (orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective s₀).trans h5.hs₀

theorem FF81Sec5.sstar_mem_nor_A₁ : t * s₀ * t⁻¹ ∈ Nor (A₁sub b b₁ b₂ b₃) :=
  Subgroup.mem_normalizer_fintype fun x hx => by
    obtain ⟨v, hv, rfl⟩ := h5.coord_of_mem_A₁ hx
    rw [h5.sstar_ε ht]
    exact h5.mem_A₁_of (by simp [S57.fs, hv])

theorem FF81Sec5.t₃_inv_β : t⁻¹ * β' b₂ b₃ * t = b₂ * b₃ := by
  rw [← h5.ε_β, h5.t₃_inv_ε ht, ← h5.ε_u₃]
  congr 1

theorem FF81Sec5.t₃_cenS {x : G} (hx : x ∈ CenS (Subgroup.closure {b₂, b₃})) (g : G)
    (hg : g = t ∨ g = t⁻¹) : g * x * g⁻¹ ∈ CenS (Subgroup.closure {b₂, b₃}) := by
  obtain ⟨h2, h3⟩ := mem_cenS_pair_iff.mp hx
  have hb2 : g * b₂ * g⁻¹ = b₂ := by
    rcases hg with rfl | rfl
    · have := ht (e 2)
      rw [h5.ε_e2, show S57.f3 (e 2) = e 2 by decide, h5.ε_e2] at this
      exact this
    · have := h5.t₃_inv_ε ht (e 2)
      rw [h5.ε_e2, show S57.f3 (e 2) = e 2 by decide, h5.ε_e2] at this
      rw [inv_inv]; exact this
  have hb3 : g * b₃ * g⁻¹ = b₃⁻¹ := by
    rcases hg with rfl | rfl
    · have := ht (e 3)
      rw [h5.ε_e3, show S57.f3 (e 3) = -e 3 by decide, h5.ε_neg, h5.ε_e3] at this
      exact this
    · have := h5.t₃_inv_ε ht (e 3)
      rw [h5.ε_e3, show S57.f3 (e 3) = -e 3 by decide, h5.ε_neg, h5.ε_e3] at this
      rw [inv_inv]; exact this
  refine mem_cenS_pair_iff.mpr ⟨?_, ?_⟩
  · have := S57.conj_comm (g := g) h2
    rwa [hb2] at this
  · have := S57.conj_comm (g := g) h3
    rw [hb3] at this
    have h' : Commute (g * x * g⁻¹) b₃⁻¹ := this
    exact (h'.inv_right).eq.trans (by rw [inv_inv]) |>.trans rfl |> fun h => by
      simpa using h

theorem FF81Sec5.J_le_cen_sstar (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀) :
    OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen (t * s₀ * t⁻¹) := by
  set Kc := CenS (Subgroup.closure {b₂, b₃}) with hKc
  set K : Subgroup G := (OUp 3 Kc).comap (MulAut.conj t⁻¹).toMonoidHom ⊓ Kc with hK
  have hmem : ∀ x, x ∈ K ↔ t⁻¹ * x * t ∈ OUp 3 Kc ∧ x ∈ Kc := fun x => by
    simp [hK, Subgroup.mem_comap, MulAut.conj_apply]
  have hle : OUp 3 Kc ≤ K := by
    refine OUp_le_of inf_le_right (fun m hm k hk => ?_) (fun m hm hc => ?_)
    · obtain ⟨hk1, hk2⟩ := (hmem k).mp hk
      refine (hmem _).mpr ⟨?_, Kc.mul_mem (Kc.mul_mem hm hk2) (Kc.inv_mem hm)⟩
      have hm' : t⁻¹ * m * t ∈ Kc := by
        simpa using h5.t₃_cenS ht hm t⁻¹ (Or.inr rfl)
      have := OUp_conj_mem hm' hk1
      have heq : t⁻¹ * (m * k * m⁻¹) * t = t⁻¹ * m * t * (t⁻¹ * k * t) * (t⁻¹ * m * t)⁻¹ := by
        group
      rw [heq]; exact this
    · refine (hmem _).mpr ⟨mem_OUp_of_coprime (by simpa using h5.t₃_cenS ht hm t⁻¹ (Or.inr rfl))
        ?_, hm⟩
      have : orderOf (t⁻¹ * m * t) = orderOf m := by
        have h := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective m
        simpa [MulAut.conj_apply] using h
      rw [this]; exact hc
  intro j hj
  obtain ⟨hj1, -⟩ := (hmem j).mp (hle hj)
  have hc := Subgroup.mem_centralizer_singleton_iff.mp (hJs hj1)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc j * (t * s₀ * t⁻¹) = t * ((t⁻¹ * j * t) * s₀) * t⁻¹ := by group
    _ = t * (s₀ * (t⁻¹ * j * t)) * t⁻¹ := by rw [hc]
    _ = t * s₀ * t⁻¹ * j := by group

end T3

section F1

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
  (hJs : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ Cen s₀)
include h5 hJs

theorem FF81Sec5.mem_β_sup {M' : Subgroup G} (hM' : M' ≤ M₅₇ b b₁ b₂ b₃ s₀) {x : G}
    (hx : x ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ M') :
    ∃ a ∈ Subgroup.zpowers (β' b₂ b₃), ∃ m ∈ M', x = a * m := by
  have hc : ∀ a ∈ Subgroup.zpowers (β' b₂ b₃), ∀ m ∈ M', a * m = m * a := fun a ha m hm => by
    have hmβ : m * β' b₂ b₃ = β' b₂ b₃ * m := Subgroup.mem_centralizer_singleton_iff.mp
      (((S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)) (hM' hm))
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((Commute.zpow_right (show Commute m (β' b₂ b₃) from hmβ) k).eq).symm
  have hnor : M' ≤ Subgroup.normalizer ((Subgroup.zpowers (β' b₂ b₃) : Subgroup G) : Set G) :=
    fun m hm => Subgroup.mem_normalizer_fintype fun a ha => by
      rw [← hc a ha m hm, mul_inv_cancel_right]; exact ha
  have hx' : x ∈ ((Subgroup.zpowers (β' b₂ b₃) ⊔ M' : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnor] at hx'
  obtain ⟨a, ha, m, hm, rfl⟩ := hx'
  exact ⟨a, ha, m, hm, rfl⟩

theorem FF81Sec5.mem_of_sq {M' : Subgroup G} (hM' : M' ≤ M₅₇ b b₁ b₂ b₃ s₀) {x : G}
    (hx : x ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ M') (h2 : x * x = 1) : x ∈ M' := by
  obtain ⟨a, ha, m, hm, rfl⟩ := h5.mem_β_sup hJs hM' hx
  have hmβ : m * β' b₂ b₃ = β' b₂ b₃ * m := Subgroup.mem_centralizer_singleton_iff.mp
    (((S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)) (hM' hm))
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hcm : Commute m (β' b₂ b₃ ^ k) := Commute.zpow_right (show Commute m (β' b₂ b₃) from hmβ) k
  have ha2 : (β' b₂ b₃ ^ k) * (β' b₂ b₃ ^ k) = (m * m)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    calc β' b₂ b₃ ^ k * β' b₂ b₃ ^ k * (m * m)
        = β' b₂ b₃ ^ k * (β' b₂ b₃ ^ k * m) * m := by group
      _ = β' b₂ b₃ ^ k * (m * β' b₂ b₃ ^ k) * m := by rw [hcm.eq]
      _ = β' b₂ b₃ ^ k * m * (β' b₂ b₃ ^ k * m) := by group
      _ = 1 := h2
  have hin : β' b₂ b₃ ^ k * β' b₂ b₃ ^ k ∈
      Subgroup.zpowers (β' b₂ b₃) ⊓ M₅₇ b b₁ b₂ b₃ s₀ :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers _ k)
      (Subgroup.zpow_mem_zpowers _ k),
      (by rw [ha2]; exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (hM' hm) (hM' hm)))⟩
  rw [h5.zpowers_β_inf_M hJs, Subgroup.mem_bot] at hin
  have h3 : (β' b₂ b₃ ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5.β_cube, one_zpow]
  have h1 : β' b₂ b₃ ^ k = 1 := by
    calc β' b₂ b₃ ^ k = (β' b₂ b₃ ^ k) ^ 3 * (β' b₂ b₃ ^ k * β' b₂ b₃ ^ k)⁻¹ := by group
      _ = 1 := by rw [h3, hin, inv_one, one_mul]
  rw [h1, one_mul]; exact hm

variable {t : G} (ht : ∀ v, t * h5.ε v * t⁻¹ = h5.ε (S57.f3 v))
include ht

theorem FF81Sec5.sstar_mem_H (hKF : KF_Sp6Levi) : t * s₀ * t⁻¹ ∈ H₅₂ b b₁ b₂ b₃ s₀ := by
  have hβ : t * s₀ * t⁻¹ * β' b₂ b₃ * (t * s₀ * t⁻¹)⁻¹ = β' b₂ b₃ := by
    rw [h5.sstar_β ht, mul_inv_cancel_right]
  obtain ⟨k, hk⟩ := h5.exists_mem_H hKF (h5.sstar_mem_nor_A₁ ht) hβ
  have hkM : β' b₂ b₃ ^ k * (t * s₀ * t⁻¹) ∈
      Subgroup.zpowers (β' b₂ b₃) ⊔ H₅₂ b b₁ b₂ b₃ s₀ :=
    Subgroup.mem_sup_right hk
  have hx2 : t * s₀ * t⁻¹ * (t * s₀ * t⁻¹) = 1 := by
    rw [← sq, ← h5.orderOf_sstar ht, pow_orderOf_eq_one]
  have hs : t * s₀ * t⁻¹ ∈ Subgroup.zpowers (β' b₂ b₃) ⊔ H₅₂ b b₁ b₂ b₃ s₀ := by
    have : t * s₀ * t⁻¹ = (β' b₂ b₃ ^ k)⁻¹ * (β' b₂ b₃ ^ k * (t * s₀ * t⁻¹)) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k))) hkM
  exact h5.mem_of_sq hJs le_sup_right hs hx2

theorem FF81Sec5.card_cen_β_sstar (c6 : IsElemAb 2 5 (Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃)))
    (hD : Cen s₀ ⊓ Cen (b₂ * b₃) = (Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃)) ⊔
      OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ⊔ Subgroup.zpowers (b₂ * b₃))
    (e : ↥(OUp 3 (CenS (Subgroup.closure {b₂, b₃}))) ≃* Equiv.Perm (Fin 6)) :
    Nat.card ↥(Cen (β' b₂ b₃) ⊓ Cen (t * s₀ * t⁻¹)) ≤ 69120 := by
  set J := OUp 3 (CenS (Subgroup.closure {b₂, b₃})) with hJ
  set u := b₂ * b₃ with hu
  have hc : ∀ {y z : G}, y * z = z * y →
      t⁻¹ * y * t * (t⁻¹ * z * t) = t⁻¹ * z * t * (t⁻¹ * y * t) :=
    fun h => by simpa using S57.conj_comm (g := t⁻¹) h
  have hle : Cen (β' b₂ b₃) ⊓ Cen (t * s₀ * t⁻¹) ≤
      (Cen s₀ ⊓ Cen u).map (MulAut.conj t).toMonoidHom := by
    intro y hy
    obtain ⟨hyβ, hys⟩ := Subgroup.mem_inf.mp hy
    have h1 := hc (Subgroup.mem_centralizer_singleton_iff.mp hyβ)
    have h2 := hc (Subgroup.mem_centralizer_singleton_iff.mp hys)
    rw [h5.t₃_inv_β ht] at h1
    rw [show t⁻¹ * (t * s₀ * t⁻¹) * t = s₀ by group] at h2
    refine ⟨t⁻¹ * y * t, Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr h2,
      Subgroup.mem_centralizer_singleton_iff.mpr h1⟩, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hJu : J ≤ Cen s₀ ⊓ Cen u := fun j hj => by
    obtain ⟨h2, h3⟩ := mem_cenS_pair_iff.mp (OUp_le _ hj)
    exact Subgroup.mem_inf.mpr ⟨hJs hj, Subgroup.mem_centralizer_singleton_iff.mpr
      ((Commute.mul_right (show Commute j b₂ from h2) (show Commute j b₃ from h3)).eq)⟩
  have hus : u ∈ Cen s₀ ⊓ Cen u :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr (h5.s₀_comm h5.u_mem_A₁),
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hnor : Cen s₀ ⊓ Cen u ≤ Subgroup.normalizer ((Op 2 (Cen s₀) ⊓ Cen u : Subgroup G) : Set G) :=
    fun y hy => Subgroup.mem_normalizer_fintype fun x hx => by
      obtain ⟨hys, hyu⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨op_two_conj hys hx1, (Cen u).mul_mem ((Cen u).mul_mem hyu hx2)
        ((Cen u).inv_mem hyu)⟩
  have hJcard : Nat.card J = 720 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hJu' : Subgroup.zpowers u ≤ Subgroup.normalizer (J : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun j hj => ?_
    have hcj := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hJu hj)).2
    rw [← hcj, mul_inv_cancel_right]; exact hj
  have h1 : Nat.card ↥(J ⊔ Subgroup.zpowers u) ≤ 2160 := by
    have := S57.card_sup_le hJu'
    rwa [hJcard, Nat.card_zpowers, h5.orderOf_u] at this
  have h2 : Nat.card ↥(Cen s₀ ⊓ Cen u) ≤ 69120 := by
    rw [hD, sup_assoc]
    have := S57.card_sup_le (N := Op 2 (Cen s₀) ⊓ Cen u) (H := J ⊔ Subgroup.zpowers u)
      ((sup_le hJu (Subgroup.zpowers_le.mpr hus)).trans hnor)
    rw [c6.2] at this
    omega
  calc Nat.card ↥(Cen (β' b₂ b₃) ⊓ Cen (t * s₀ * t⁻¹))
      ≤ Nat.card ↥((Cen s₀ ⊓ Cen u).map (MulAut.conj t).toMonoidHom) := Subgroup.card_le_of_le hle
    _ = Nat.card ↥(Cen s₀ ⊓ Cen u) := Subgroup.card_map_of_injective (MulAut.conj t).injective
    _ ≤ 69120 := h2

theorem FF81Sec5.cen_β_sstar (hKF : KF_Sp6Levi) (hCls : KF_Sp6Cls)
    (hmod : StatedClassicalModel (M₅₇ b b₁ b₂ b₃ s₀) .PSp 3 2 1)
    (c6 : IsElemAb 2 5 (Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃)))
    (hD : Cen s₀ ⊓ Cen (b₂ * b₃) = (Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃)) ⊔
      OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ⊔ Subgroup.zpowers (b₂ * b₃))
    (e : ↥(OUp 3 (CenS (Subgroup.closure {b₂, b₃}))) ≃* Equiv.Perm (Fin 6)) :
    t * s₀ * t⁻¹ ∈ M₅₇ b b₁ b₂ b₃ s₀ ∧
    Nat.card ↥(M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (t * s₀ * t⁻¹)) = 23040 ∧
    Cen (β' b₂ b₃) ⊓ Cen (t * s₀ * t⁻¹) =
      Subgroup.zpowers (β' b₂ b₃) ⊔ (M₅₇ b b₁ b₂ b₃ s₀ ⊓ Cen (t * s₀ * t⁻¹)) := by
  set M := M₅₇ b b₁ b₂ b₃ s₀ with hM
  set s := t * s₀ * t⁻¹ with hs
  have hsM : s ∈ M := Subgroup.mem_sup_right (h5.sstar_mem_H hJs ht hKF)
  have hJ : OUp 3 (CenS (Subgroup.closure {b₂, b₃})) ≤ M ⊓ Cen s :=
    le_inf le_sup_left (h5.J_le_cen_sstar ht hJs)
  have h5d : 5 ∣ Nat.card ↥(M ⊓ Cen s) :=
    (show 5 ∣ 720 by norm_num).trans (S57.card_J e ▸ Subgroup.card_dvd_of_le hJ)
  have hcard := ((hCls G M hmod).2.2.2.2 s hsM (h5.orderOf_sstar ht) h5d).1
  refine ⟨hsM, hcard, ?_⟩
  have hMβ : M ≤ Cen (β' b₂ b₃) := (S57.M_le_cenS hJs).trans (S57.cenS_pair_le_left _ _)
  have hβs : β' b₂ b₃ ∈ Cen s :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h5.sstar_β ht).symm
  have hle : Subgroup.zpowers (β' b₂ b₃) ⊔ (M ⊓ Cen s) ≤ Cen (β' b₂ b₃) ⊓ Cen s :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hβs⟩))
      (inf_le_inf_right _ hMβ)
  have hc : ∀ x ∈ Subgroup.zpowers (β' b₂ b₃), ∀ y ∈ M ⊓ Cen s, x * y = y * x :=
    fun x hx y hy => by
    have hyβ : y * β' b₂ b₃ = β' b₂ b₃ * y :=
      Subgroup.mem_centralizer_singleton_iff.mp (hMβ (Subgroup.mem_inf.mp hy).1)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_right (show Commute y (β' b₂ b₃) from hyβ) k).eq).symm
  have hinf : Subgroup.zpowers (β' b₂ b₃) ⊓ (M ⊓ Cen s) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_left).trans (h5.zpowers_β_inf_M hJs).le)
  have hsup := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, h5.β_orderOf, hcard] at hsup
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hsup]
  exact h5.card_cen_β_sstar hJs ht c6 hD e

end F1

end CFSG.RankThree.PartTwo.Sec21.FF81
