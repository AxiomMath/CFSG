module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4BstarRankTri
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin

public section

namespace CFSG.StandardType

namespace D4Bstar

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

section Center

variable {G : Type} [Group G] {U : Type*} [Group U]

theorem eq_one_of_mem_range_centralizer {ψ : U →* G} (hker : ψ.ker ≤ Subgroup.center U)
    (hZ : Subgroup.center U = ⊥) {z : G} (hz : z ∈ ψ.range)
    (hzc : z ∈ Subgroup.centralizer (ψ.range : Set G)) : z = 1 := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  obtain ⟨u, rfl⟩ := hz
  have hu : u ∈ Subgroup.center U := by
    rw [Subgroup.mem_center_iff]
    intro v
    apply hinj
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hzc (ψ v) ⟨v, rfl⟩
  rw [hZ, Subgroup.mem_bot] at hu
  rw [hu, map_one]

end Center

section Inner

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem mem_ggG0_of_psiInnerDiag (hcfg : GGConfig 3 B Bs x L D J) {f : ℕ}
    {ψ : (ggU .POmegaPlus 4 f).K →* G}
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ)
    (hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) {b : G} (hb : b ∈ Bs)
    (hd : GGPsiInnerDiag (ggU .POmegaPlus 4 f).D ψ b) : b ∈ ggG0 3 B x L D J := by
  set G₀ := ggG0 3 B x L D J with hG₀
  obtain ⟨g, hg, hbg⟩ := ggPsiDiagInner_POmegaPlus G 4 f ψ G₀ hpres b (hBsN hb) hd
  have hrange : ψ.range = G₀ := hpres.2.1.1
  have hZ : ∀ z ∈ G₀, z ∈ Subgroup.centralizer (G₀ : Set G) → z = 1 := by
    intro z hz hzc
    rw [← hrange] at hz hzc
    exact eq_one_of_mem_range_centralizer hpres.2.1.2
      (RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := GaloisField 2 f) (n := 4)
        (by norm_num)) hz hzc
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hcomm : ∀ a ∈ Bs, ∀ a' ∈ Bs, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hbgc : b * g = g * b := by
    have h1 := Subgroup.mem_centralizer_iff.mp hbg g hg
    have h2 : g * b * g = b * g * g := by rw [mul_assoc]; exact h1
    exact (mul_right_cancel h2).symm
  have hd3 : (b * g) ^ 3 = 1 := by
    have hpow : (b * g) ^ 3 = b ^ 3 * g ^ 3 := Commute.mul_pow hbgc 3
    have hb3 : b ^ 3 = 1 := hBs.2 b hb
    rw [hb3, one_mul] at hpow
    have hg3 : g ^ 3 = 1 := hZ _ (pow_mem hg 3) (hpow ▸ pow_mem hbg 3)
    rw [hpow, hg3]
  have hdC : b * g ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b' hb'
    have hb'N := hBsN hb'
    have hg'G : b' * g * b'⁻¹ ∈ G₀ := (Subgroup.mem_normalizer_iff.mp hb'N g).mp hg
    have he : b' * (b * g) * b'⁻¹ ∈ Subgroup.centralizer (G₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : b'⁻¹ * z * b' ∈ G₀ := by
        have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hb'N) z).mp hz
        rwa [inv_inv] at h
      have hc := Subgroup.mem_centralizer_iff.mp hbg _ hz'
      calc z * (b' * (b * g) * b'⁻¹) = b' * ((b'⁻¹ * z * b') * (b * g)) * b'⁻¹ := by group
        _ = b' * ((b * g) * (b'⁻¹ * z * b')) * b'⁻¹ := by rw [hc]
        _ = b' * (b * g) * b'⁻¹ * z := by group
    have he' : b' * (b * g) * b'⁻¹ = b * (b' * g * b'⁻¹) := by
      calc b' * (b * g) * b'⁻¹ = (b' * b) * g * b'⁻¹ := by group
        _ = (b * b') * g * b'⁻¹ := by rw [hcomm b' hb' b hb]
        _ = b * (b' * g * b'⁻¹) := by group
    have hq : g⁻¹ * (b' * g * b'⁻¹) = 1 := by
      refine hZ _ (mul_mem (inv_mem hg) hg'G) ?_
      have e : (b * g)⁻¹ * (b' * (b * g) * b'⁻¹) = g⁻¹ * (b' * g * b'⁻¹) := by
        rw [he']
        group
      rw [← e]
      exact mul_mem (inv_mem hbg) he
    have hgg : g = b' * g * b'⁻¹ := inv_mul_eq_one.mp hq
    have hfix : b' * (b * g) * b'⁻¹ = b * g := by rw [he', ← hgg]
    calc b' * (b * g) = b' * (b * g) * b'⁻¹ * b' := by group
      _ = b * g * b' := by rw [hfix]
  have hdBs : b * g ∈ Bs := hcfg.2.1.2.2.2 _ hdC hd3
  have hbot := bstar_inf_centralizer_ggG0_eq_bot hcfg
  have hd1 : b * g = 1 := by
    have hmem : b * g ∈ Bs ⊓ Subgroup.centralizer (G₀ : Set G) := ⟨hdBs, hbg⟩
    rw [hG₀, hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  rw [eq_inv_of_mul_eq_one_left hd1]
  exact inv_mem hg

theorem semilinear_of_torusOnRoot (hcfg : GGConfig 3 B Bs x L D J) {f : ℕ}
    {ψ : (ggU .POmegaPlus 4 f).K →* G}
    (hpres : GGPresentsG0 (ggG0 3 B x L D J) (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ)
    (hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G))
    {γ : Fin (ggU .POmegaPlus 4 f).D.rank → ℤ} (hγ : γ ∈ (ggU .POmegaPlus 4 f).D.roots)
    {u : (ggU .POmegaPlus 4 f).K}
    (hall : ∀ b ∈ Bs, GGTorusOnRoot (ggU .POmegaPlus 4 f).D ψ b γ u) :
    ∀ b ∈ Bs, GGSpinSemilinear (quadPlus 4 (GaloisField 2 f)) ψ b := by
  intro b₁ hb₁
  by_contra hns
  have hrange : ψ.range = ggG0 3 B x L D J := hpres.2.1.1
  have hinj : Function.Injective ψ :=
    injective_of_ker_le_center (F := GaloisField 2 f) hpres.2.1.2
  obtain ⟨-, hBs, -, -, h81⟩ := hcfg.tableB_facts
  have hN : ∀ b ∈ Bs, b ∈ Subgroup.normalizer (ψ.range : Set G) := fun b hb =>
    mem_normalizer_range_of_bstar hrange hBsN hb
  have hC3 : ∀ b ∈ Bs, b ^ 3 ∈ Subgroup.centralizer (ψ.range : Set G) := fun b hb =>
    pow_mem_centralizer_range_of_bstar hcfg ψ hb
  have hA : ∀ b ∈ Bs, GGSpinSemilinear (quadPlus 4 (GaloisField 2 f)) ψ b →
      b ∈ ggG0 3 B x L D J := fun b hb hs =>
    mem_ggG0_of_psiInnerDiag hcfg hpres hBsN hb
      (ggPsiInnerDiag_D4_of_semilinear hpres.2.1.2 Nat.prime_three (by norm_num) (hN b hb)
        (hC3 b hb) hγ (hall b hb) hs)
  have hcomm : ∀ a ∈ Bs, ∀ a' ∈ Bs, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hE : IsElemAbelian 3 (Bs ⊓ ggG0 3 B x L D J) :=
    ⟨⟨⟨fun a a' => Subtype.ext (hcomm _ a.2.1 _ a'.2.1)⟩⟩, fun a ha => hBs.2 a ha.1⟩
  have hEc : Bs ⊓ ggG0 3 B x L D J ≤ Subgroup.centralizer ({b₁} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm a ha.1 b₁ hb₁
  have hEψ : Bs ⊓ ggG0 3 B x L D J ≤ ψ.range := by
    rw [hrange]
    exact inf_le_right
  have h9 := ggD4TrialityCentRankInput_holds G f ψ hpres.1.1.2.1 hpres.2.1.2 b₁ (hN b₁ hb₁)
    (hC3 b₁ hb₁) hns _ hEψ hEc hE
  have hj : ∀ a : Bs, ∃ j : Fin 3, (a : G) * b₁ ^ (j : ℕ) ∈ Bs ⊓ ggG0 3 B x L D J := by
    intro a
    obtain ⟨j, hj3, hjs⟩ := exists_semilinear_mul_pow hinj (hN a a.2) (hN b₁ hb₁) (hC3 a a.2)
      (hC3 b₁ hb₁) hns
    have hmem : (a : G) * b₁ ^ j ∈ Bs := mul_mem a.2 (pow_mem hb₁ j)
    exact ⟨⟨j, hj3⟩, hmem, hA _ hmem hjs⟩
  choose j hjE using hj
  have hinjF : Function.Injective fun a : Bs =>
      ((⟨(a : G) * b₁ ^ (j a : ℕ), hjE a⟩ : ↥(Bs ⊓ ggG0 3 B x L D J)), j a) := by
    intro a a' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1' : (a : G) * b₁ ^ (j a : ℕ) = (a' : G) * b₁ ^ (j a' : ℕ) := congrArg Subtype.val h1
    rw [h2] at h1'
    exact Subtype.ext (mul_right_cancel h1')
  have hle := Nat.card_le_card_of_injective _ hinjF
  rw [Nat.card_prod, Nat.card_fin] at hle
  have h27 : Nat.card Bs ≤ 27 :=
    hle.trans (by simpa using Nat.mul_le_mul_right 3 h9)
  have h81' : 81 ≤ Nat.card Bs := by simpa using h81
  omega

end Inner

end D4Bstar

end CFSG.StandardType
