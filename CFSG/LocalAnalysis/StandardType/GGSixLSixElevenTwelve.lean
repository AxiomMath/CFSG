module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenDiff
public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenComm
public import CFSG.LocalAnalysis.StandardType.GGSixLSixElevenAlperin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Coords

variable {G : Type} [Group G] {p : ℕ} {Bs G₀ : Subgroup G} {f : ℕ} {z : G}
  {v : G → ZMod p → ZMod p}

theorem GGTorusCoords.const_one (hc : GGTorusCoords p Bs G₀ f z v) : ∃ c, ∀ j, v 1 j = c := by
  obtain ⟨c, hc1⟩ := hc.1 1 Bs.one_mem 1 Bs.one_mem
  refine ⟨-c, fun j => ?_⟩
  have := hc1 j
  rw [mul_one] at this
  linear_combination -this

theorem GGTorusCoords.secondDiff (hc : GGTorusCoords p Bs G₀ f z v)
    (hzN : z ∈ Subgroup.normalizer (Bs : Set G)) {e : G} (he : e ∈ Bs)
    (hcomm : z⁻¹ * (e⁻¹ * (z⁻¹ * e * z)) * z = e⁻¹ * (z⁻¹ * e * z)) :
    ∃ C : ZMod p, ∀ j, v e (j + 2) - 2 * v e (j + 1) + v e j = C := by
  have hze : z⁻¹ * e * z ∈ Bs := conj_inv_mem_of_mem_normalizer hzN he
  have hr : e⁻¹ * (z⁻¹ * e * z) ∈ Bs := Bs.mul_mem (Bs.inv_mem he) hze
  obtain ⟨c₄, h4⟩ := hc.2.2.1 _ hr
  rw [hcomm] at h4
  obtain ⟨c₅, h5⟩ := hc.1 _ (Bs.inv_mem he) _ hze
  obtain ⟨c₆, h6⟩ := hc.1 _ (Bs.inv_mem he) _ he
  obtain ⟨c₇, h7⟩ := hc.const_one
  obtain ⟨c₈, h8⟩ := hc.2.2.1 _ he
  have hinv : ∀ j, v e⁻¹ j = c₇ - v e j - c₆ := by
    intro j
    have := h6 j
    rw [inv_mul_cancel, h7] at this
    linear_combination -this
  have hrv : ∀ j, v (e⁻¹ * (z⁻¹ * e * z)) j = c₇ - c₆ + c₈ + c₅ + v e (j + 1) - v e j := by
    intro j
    rw [h5 j, hinv j, h8 j]
    ring
  refine ⟨-c₄, fun j => ?_⟩
  have h := h4 j
  rw [hrv j, hrv (j + 1), show j + 1 + 1 = j + 2 by ring] at h
  linear_combination -h

end Coords

section Helpers

variable {G : Type} [Group G]

theorem conj_pow_eq_one {p : ℕ} {b : G} (hb : b ^ p = 1) (k : G) : (k⁻¹ * b * k) ^ p = 1 := by
  have h := map_pow (MulAut.conj k⁻¹) b p
  simp only [MulAut.conj_apply, inv_inv] at h
  rw [← h, hb, mul_one, inv_mul_cancel]

end Helpers

section Core

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {Bs G₀ : Subgroup G}
  {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ} {ψ : U →* G}

theorem GGSixFusionSetting.exists_conj_mem_sylow (hS : GGSixFusionSetting p Bs G₀ Δ t n f ψ)
    (P : Sylow p G) (hPM : (P : Subgroup G) ≤ Subgroup.normalizer (G₀ : Set G)) {b : G}
    (hb : b ∈ Bs) (hb1 : b ≠ 1) {g : G} (hg : g⁻¹ * b * g ∈ Subgroup.normalizer (G₀ : Set G))
    (hgM : g ∉ Subgroup.normalizer (G₀ : Set G)) :
    ∃ g' : G, g'⁻¹ * b * g' ∈ (P : Subgroup G) ∧ g' ∉ Subgroup.normalizer (G₀ : Set G) := by
  have : Fact p.Prime := ⟨hS.prime⟩
  set M := Subgroup.normalizer (G₀ : Set G) with hM
  set P' : Sylow p M := P.subtype hPM with hP'
  set y : M := ⟨g⁻¹ * b * g, hg⟩ with hy
  have hyo : orderOf y = p := by
    rw [hy, Subgroup.orderOf_mk]
    exact hS.orderOf_conj hb hb1 g
  have hyp : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  obtain ⟨R, hR⟩ := hyp.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M R P'
  have hmem : MulAut.conj m y ∈ ((m • R : Sylow p M) : Subgroup M) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR (Subgroup.mem_zpowers y))
  rw [hm, hP', Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hmem
  refine ⟨g * (m : G)⁻¹, ?_, fun h => hgM ?_⟩
  · have heq : (g * (m : G)⁻¹)⁻¹ * b * (g * (m : G)⁻¹) = ((MulAut.conj m y : M) : G) := by
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hy]
      group
    rw [heq]
    exact hmem
  · have := M.mul_mem h m.2
    rwa [inv_mul_cancel_right] at this

theorem GGSixFusionSetting.not_typeAk_of_conj (hS : GGSixFusionSetting p Bs G₀ Δ t n f ψ)
    (hQ : ∀ Q : Subgroup G, Q ≤ Subgroup.normalizer (Bs : Set G) → IsPGroup p Q →
      IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) ∧
        Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)))
    (hv : ∀ z ∈ Subgroup.normalizer (Bs : Set G), z ∉ Subgroup.centralizer (Bs : Set G) →
      z ^ p = 1 → ∃ v : G → ZMod p → ZMod p, GGTorusCoords p Bs G₀ f z v)
    {b : G} (hb : b ∈ Bs) (hCb : Subgroup.centralizer {b} ≤ Subgroup.normalizer (G₀ : Set G))
    {g : G} (hg : g⁻¹ * b * g ∈ Subgroup.normalizer (G₀ : Set G))
    (hgM : g ∉ Subgroup.normalizer (G₀ : Set G))
    (hK : ∃ K : Subgroup G, IsComponentOf K (G₀ ⊓ Subgroup.centralizer {b}) ∧ GGTypeAk f K) :
    False := by
  classical
  have : Fact p.Prime := ⟨hS.prime⟩
  set M := Subgroup.normalizer (G₀ : Set G) with hM
  have hb1 : b ≠ 1 := ne_one_of_centralizer_le hCb hgM
  have hbp : b ^ p = 1 := hS.elem.2 b hb
  obtain ⟨P, hBsP, hPM, huniq⟩ := hS.exists_sylow
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (Bs : Set G) := by
    intro u hu
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (huniq _ ?_
      (isElemAbelian_map_hom hS.elem _) (Subgroup.card_map_of_injective (MulAut.conj u).injective))
    rintro _ ⟨a, ha, rfl⟩
    exact (P : Subgroup G).mul_mem ((P : Subgroup G).mul_mem hu (hBsP ha))
      ((P : Subgroup G).inv_mem hu)
  obtain ⟨g', hg'P, hg'M⟩ := hS.exists_conj_mem_sylow P hPM hb hb1 hg hgM
  set Good : G → Prop := fun w => ∃ m ∈ M, m⁻¹ * w * m ∈ Bs with hGood
  have hbad : ¬ Good (g'⁻¹ * b * g') := fun ⟨m, hm, hmem⟩ =>
    hS.not_conj_mem hb hCb hg'M m hm hmem
  have hbb : (g'⁻¹)⁻¹ * (g'⁻¹ * b * g') * g'⁻¹ = b := by group
  have hgoodb : Good ((g'⁻¹)⁻¹ * (g'⁻¹ * b * g') * g'⁻¹) :=
    ⟨1, M.one_mem, by rw [hbb]; simpa using hb⟩
  obtain ⟨Q, hQP, z, hzQ, n₀, hn₀, hzbad, hegood, c, hzc⟩ :=
    exists_good_step_of_conj P Good hg'P (by rw [hbb]; exact hBsP hb) hgoodb hbad
  set e := n₀⁻¹ * z * n₀ with he_def
  have heQ : e ∈ Q := conj_inv_mem_of_mem_normalizer hn₀ hzQ
  have hzP : z ∈ (P : Subgroup G) := hQP hzQ
  have heP : e ∈ (P : Subgroup G) := hQP heQ
  have hzN : z ∈ Subgroup.normalizer (Bs : Set G) := hPN hzP
  have heN : e ∈ Subgroup.normalizer (Bs : Set G) := hPN heP
  have hzconj : z = (g' * c)⁻¹ * b * (g' * c) := by rw [hzc]; group
  have hzp : z ^ p = 1 := hzconj ▸ conj_pow_eq_one hbp _
  have heconj : e = (g' * c * n₀)⁻¹ * b * (g' * c * n₀) := by rw [he_def, hzconj]; group
  have hep : e ^ p = 1 := heconj ▸ conj_pow_eq_one hbp _
  have hzC : z ∉ Subgroup.centralizer (Bs : Set G) := fun h =>
    hzbad ⟨1, M.one_mem, by simpa using hS.omega z h hzp⟩
  obtain ⟨m₁, hm₁, hm₁e⟩ := hegood
  have hb₁ : (g' * c * n₀ * m₁)⁻¹ * b * (g' * c * n₀ * m₁) ∈ Bs := by
    have : (g' * c * n₀ * m₁)⁻¹ * b * (g' * c * n₀ * m₁) = m₁⁻¹ * e * m₁ := by
      rw [heconj]; group
    rw [this]
    exact hm₁e
  obtain ⟨k, hk, hkeq⟩ := hS.conj_eq hb hb₁
  set m' := k * m₁⁻¹ with hm'
  have hm'M : m' ∈ M := M.mul_mem (hS.normalizer_le hk) (M.inv_mem hm₁)
  have hem : e = m'⁻¹ * b * m' := by
    have h1 : m₁⁻¹ * e * m₁ = k⁻¹ * b * k := by
      rw [← hkeq, heconj]; group
    calc e = m₁ * (m₁⁻¹ * e * m₁) * m₁⁻¹ := by group
      _ = m₁ * (k⁻¹ * b * k) * m₁⁻¹ := by rw [h1]
      _ = m'⁻¹ * b * m' := by rw [hm']; group
  have hbm : m' * e * m'⁻¹ = b := by rw [hem]; group
  obtain ⟨v, hv⟩ := hv z hzN hzC hzp
  have htripb : GGHasTripleValue (v b) :=
    hv.2.2.2.2 b hb 1 M.one_mem (by rw [show (1 : G) * b * 1⁻¹ = b by group]; exact hK)
  have heC : e ∈ Subgroup.centralizer (Bs : Set G) := by
    by_contra heC
    have hinj := hv.2.2.2.1 e heN heC hep m'⁻¹ (M.inv_mem hm'M)
      (by rw [inv_inv, hbm]; exact hb)
    rw [inv_inv, hbm] at hinj
    obtain ⟨j₁, j₂, -, h12, -, -, he2, -⟩ := htripb
    exact h12 (hinj he2)
  have heBs : e ∈ Bs := hS.omega e heC hep
  obtain ⟨hAc, hQcard⟩ := hQ Q (hQP.trans hPN) (P.isPGroup'.to_le hQP)
  have heA : e ∈ Q ⊓ Subgroup.centralizer (Bs : Set G) := ⟨heQ, heC⟩
  have hzA : z ∈ Subgroup.normalizer ((Q ⊓ Subgroup.centralizer (Bs : Set G) : Subgroup G) :
      Set G) := by
    have hzQN : z ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hzQ
    have hzCN := mem_normalizer_centralizer hzN
    rw [Subgroup.mem_normalizer_iff] at hzQN hzCN ⊢
    intro a
    simp only [Subgroup.mem_inf]
    rw [hzQN a, hzCN a]
  have hcardz : Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer {z}) := by
    have hA : Q ⊓ Subgroup.centralizer (Bs : Set G) ≤ Q ⊓ Subgroup.centralizer {e} :=
      fun a ha => ⟨ha.1, Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp ha.2) e heBs).symm⟩
    have hmap : (Q ⊓ Subgroup.centralizer {e}).map (MulAut.conj n₀).toMonoidHom ≤
        Q ⊓ Subgroup.centralizer {z} := by
      rintro _ ⟨a, ⟨haQ, hae⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine ⟨(Subgroup.mem_normalizer_iff.mp hn₀ a).mp haQ, ?_⟩
      have hae' : a ∈ Subgroup.centralizer {e} := hae
      show n₀ * a * n₀⁻¹ ∈ Subgroup.centralizer {z}
      rw [Subgroup.mem_centralizer_singleton_iff] at hae' ⊢
      have hz' : z = n₀ * e * n₀⁻¹ := by rw [he_def]; group
      rw [hz']
      calc n₀ * a * n₀⁻¹ * (n₀ * e * n₀⁻¹) = n₀ * (a * e) * n₀⁻¹ := by group
        _ = n₀ * (e * a) * n₀⁻¹ := by rw [hae']
        _ = n₀ * e * n₀⁻¹ * (n₀ * a * n₀⁻¹) := by group
    have h1 := Subgroup.card_le_of_le hA
    have h2 := Subgroup.card_le_of_le hmap
    rw [Subgroup.card_map_of_injective (MulAut.conj n₀).injective] at h2
    calc Nat.card Q ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer (Bs : Set G)) := hQcard
      _ ≤ p * Nat.card ↥(Q ⊓ Subgroup.centralizer {z}) :=
        Nat.mul_le_mul_left _ (h1.trans h2)
  have hcomm := conj_comm_eq_of_card_le inf_le_left hAc hzA (P.isPGroup'.to_le hQP) hzp
    hcardz heA
  obtain ⟨C, hC⟩ := hv.secondDiff hzN heBs hcomm
  obtain ⟨j₁, j₂, j₃, h12, h13, h23, he2, he3⟩ :=
    hv.2.2.2.2 e heBs m' hm'M (by rw [hbm]; exact hK)
  have hconst := eq_zero_of_secondDiff hS.ne_two (v e) C hC h12 h13 h23 he2 he3
  have he1 : e = 1 := hv.2.1 e heBs ⟨v e 0, hconst⟩
  apply hb1
  rw [← hbm, he1]
  group

end Core

section Inputs

theorem ggSixLSixTwelveInput_of_kg (hRk : GGSixLinearRankInput)
    (hTM : GGSixLinearTorusModelInput) : GGSixLSixTwelveInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx hC hU b hb hCb g hg hgM hlin
  have hS := hctx.fusionSetting hC hU
  have hb1 : b ≠ 1 := ne_one_of_centralizer_le hCb hgM
  have hcard : Nat.card Bs = p ^ (p - 1) :=
    hRk G p Bs _ t n f ψ hS hlin (g⁻¹ * b * g) hg (hS.orderOf_conj hb hb1 g)
      (hS.not_conj_mem hb hCb hgM)
  obtain ⟨hQ, hv⟩ := hTM G p Bs _ t n f ψ hS hlin hcard
  exact ⟨hcard, fun K hK hKA => hS.not_typeAk_of_conj hQ hv hb hCb hg hgM ⟨K, hK, hKA⟩⟩

end Inputs

end CFSG.StandardType
