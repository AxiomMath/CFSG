module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInner
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenUnitaryIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGTorusNbrSC (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ∀ Y : Subgroup (MulAut L'),
          (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          (∀ n ∈ W, ∀ φ ∈ Y, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Y) →
          (∀ φ ∈ Y, ∀ a ∈ A, φ * a * φ⁻¹ ∈ A) →
          (∀ φ ∈ Y, ∃ k : ℕ, ∀ a ∈ A, φ ^ p ^ k * a = a * φ ^ p ^ k) →
          ∀ φ ∈ Y, ∀ a ∈ A, φ * a = a * φ

theorem ggTorusNbrSC_of_card_lt {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ∀ A : Subgroup (MulAut L'),
        IsElemAbelian p A → (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
          Nat.card A < p ^ 3) :
    GGTorusNbrSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 _
  exact absurd (h L' ψ hψ hker hperf A hA hAI) (not_lt.mpr h3)

namespace NbrInnerRest

theorem forall_comm_of_irred {p : ℕ} (hp : p.Prime) {L' : Type} [Group L'] [Finite L']
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (h3 : p ^ 3 ≤ Nat.card A) {W : Set L'}
    (hW2 : ∀ A' : Subgroup (MulAut L'), A' ≤ A →
      (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → A' = ⊥ ∨ A' = A)
    (Y : Subgroup (MulAut L'))
    (hWA : ∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A)
    (hWY : ∀ n ∈ W, ∀ φ ∈ Y, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Y)
    (hYA : ∀ φ ∈ Y, ∀ a ∈ A, φ * a * φ⁻¹ ∈ A)
    (hYp : ∀ φ ∈ Y, ∃ k : ℕ, ∀ a ∈ A, φ ^ p ^ k * a = a * φ ^ p ^ k) :
    ∀ φ ∈ Y, ∀ a ∈ A, φ * a = a * φ := by
  have := Fact.mk hp
  set A' : Subgroup (MulAut L') := A ⊓ Subgroup.centralizer (Y : Set (MulAut L')) with hA'
  have hA'inv : ∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A' := by
    intro n hn a ha
    refine ⟨hWA n hn a ha.1, Subgroup.mem_centralizer_iff.mpr fun φ hφ => ?_⟩
    have hχ := inv_conj_mem_of_conj_mem (hWY n hn) hφ
    have hc := Subgroup.mem_centralizer_iff.mp ha.2 _ hχ
    set c := MulAut.conj n
    calc φ * (c * a * c⁻¹) = c * ((c⁻¹ * φ * c) * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * φ * c)) * c⁻¹ := by rw [hc]
      _ = c * a * c⁻¹ * φ := by group
  rcases hW2 A' inf_le_left hA'inv with hbot | htop
  · exfalso
    have hA1 : Nat.card A ≠ 1 := by
      intro h1
      rw [h1] at h3
      have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    obtain ⟨a, ha, ha1, hac⟩ :=
      exists_ne_one_forall_comm_of_pGroup (isPGroup_of_isElemAbelian hA) hA1 hYA hYp
    have haA' : a ∈ A' := ⟨ha, Subgroup.mem_centralizer_iff.mpr hac⟩
    rw [hbot] at haA'
    exact ha1 (Subgroup.mem_bot.mp haA')
  · intro φ hφ a ha
    have haA' : a ∈ A' := htop ▸ ha
    exact Subgroup.mem_centralizer_iff.mp haA'.2 φ hφ

end NbrInnerRest

open NbrInnerRest

theorem ggTorusNbrSC_of_ggTorusIrredSC {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : CorFourTwoOpen.GGTorusIrredSC p R I) : GGTorusNbrSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  obtain ⟨W, hW1, hW2, -, -⟩ := h L' ψ hψ hker hperf A hA hAI h3 hsc
  exact ⟨W, hW1, forall_comm_of_irred hp hA h3 hW2⟩

theorem ggTorusNbrSC_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGTorusNbrSC p R' I') : GGTorusNbrSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ h3 hsc
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]

section Config

variable {G : Type} [Group G] [Finite G]

namespace NbrInnerRest

theorem ggTableBNbrInner_of_weyl {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {W : Set K}
    (hW1 : ∀ n ∈ W, ∀ a ∈ (ggGamma K hN).range, (n * (a n)⁻¹) ^ p = 1 ∧
      ∀ a' ∈ (ggGamma K hN).range, a' (n * (a n)⁻¹) = n * (a n)⁻¹)
    (hW2 : ∀ Y : Subgroup (MulAut K),
      (∀ n ∈ W, ∀ a ∈ (ggGamma K hN).range,
        MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ (ggGamma K hN).range) →
      (∀ n ∈ W, ∀ φ ∈ Y, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Y) →
      (∀ φ ∈ Y, ∀ a ∈ (ggGamma K hN).range, φ * a * φ⁻¹ ∈ (ggGamma K hN).range) →
      (∀ φ ∈ Y, ∃ k : ℕ, ∀ a ∈ (ggGamma K hN).range, φ ^ p ^ k * a = a * φ ^ p ^ k) →
      ∀ φ ∈ Y, ∀ a ∈ (ggGamma K hN).range, φ * a = a * φ)
    {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (Bs : Set G)) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYn : ∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      ∀ g ∈ Y, n * g * n⁻¹ ∈ Y)
    (hYp : ∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) :
    ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  classical
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hnb.1.2.2.2.1
  set γ := ggGamma K hN with hγ
  have hWB : ∀ n ∈ W, ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro n hn b hb
    obtain ⟨htp, htA⟩ := hW1 n hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : K) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hWN : ∀ n ∈ W, (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    intro n hn
    have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
      simpa using hWB n hn w hw)
    simpa using Subgroup.inv_mem _ h
  set Ybar : Subgroup (MulAut K) :=
    (Y.subgroupOf (Subgroup.normalizer (K : Set G))).map K.normalizerMonoidHom with hYbar
  have hgB : ∀ g ∈ Y, ∀ b : Bs, (g : G) * b * g⁻¹ ∈ Bs := fun g hg b =>
    (Subgroup.mem_normalizer_iff.mp (hYN hg) b).mp b.2
  have hWA : ∀ n ∈ W, ∀ a ∈ γ.range, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ γ.range := by
    rintro n hn _ ⟨b, rfl⟩
    exact ⟨⟨(n : G) * b * (n : G)⁻¹, hWB n hn b b.2⟩,
      (ggGamma_conj K hN n b (hWB n hn b b.2)).symm ▸ rfl⟩
  have hWY : ∀ n ∈ W, ∀ φ ∈ Ybar, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Ybar := by
    rintro n hn _ ⟨g, hg, rfl⟩
    rw [conj_mul_normalizerMonoidHom]
    refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    exact hYn n ⟨hWN n hn, hKy n.2⟩ g (Subgroup.mem_subgroupOf.mp hg)
  have hYA : ∀ φ ∈ Ybar, ∀ a ∈ γ.range, φ * a * φ⁻¹ ∈ γ.range := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨_, (normalizerMonoidHom_mul_ggGamma K hN g b
      (hgB g (Subgroup.mem_subgroupOf.mp hg) b)).symm⟩
  have hYpA : ∀ φ ∈ Ybar, ∃ k : ℕ, ∀ a ∈ γ.range, φ ^ p ^ k * a = a * φ ^ p ^ k := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨k, hk⟩ := hYp g (Subgroup.mem_subgroupOf.mp hg)
    refine ⟨k, ?_⟩
    rintro _ ⟨b, rfl⟩
    rw [← map_pow]
    have hb' : ((g ^ p ^ k : Subgroup.normalizer (K : Set G)) : G) * b *
        ((g ^ p ^ k : Subgroup.normalizer (K : Set G)) : G)⁻¹ = b := by
      push_cast
      rw [(Subgroup.mem_centralizer_iff.mp hk b b.2).symm, mul_inv_cancel_right]
    have h1 := normalizerMonoidHom_mul_ggGamma K hN (g ^ p ^ k) b (hb'.symm ▸ b.2)
    have h2 : ggGamma K hN ⟨((g ^ p ^ k : Subgroup.normalizer (K : Set G)) : G) * b *
        ((g ^ p ^ k : Subgroup.normalizer (K : Set G)) : G)⁻¹, hb'.symm ▸ b.2⟩ = γ b := by
      congr 1
      exact Subtype.ext hb'
    rw [h2] at h1
    calc K.normalizerMonoidHom (g ^ p ^ k) * γ b
        = K.normalizerMonoidHom (g ^ p ^ k) * γ b * (K.normalizerMonoidHom (g ^ p ^ k))⁻¹ *
          K.normalizerMonoidHom (g ^ p ^ k) := by group
      _ = γ b * K.normalizerMonoidHom (g ^ p ^ k) := by rw [h1]
  have hcomm := hW2 Ybar hWA hWY hYA hYpA
  intro g hg b hb
  have h1 := hcomm _ ⟨⟨g, hYK hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩ (γ ⟨b, hb⟩)
    ⟨⟨b, hb⟩, rfl⟩
  have h2 := normalizerMonoidHom_mul_ggGamma K hN ⟨g, hYK hg⟩ ⟨b, hb⟩ (hgB g hg ⟨b, hb⟩)
  rw [h1, mul_inv_cancel_right] at h2
  have h3 : γ (⟨g * b * g⁻¹, hgB g hg ⟨b, hb⟩⟩ * (⟨b, hb⟩ : Bs)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h2, mul_inv_cancel]
  exact (ggGamma_eq_one_iff K hN _).mp h3

end NbrInnerRest

open NbrInnerRest

theorem ggTableBNbrInner_of_ggTorusNbrSC {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hT : GGTorusNbrSC p R I) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (Bs : Set G)) (hYK : Y ≤ Subgroup.normalizer (K : Set G))
    (hYn : ∀ n ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({y} : Set G),
      ∀ g ∈ Y, n * g * n⁻¹ ∈ Y)
    (hYp : ∀ g ∈ Y, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) :
    ∀ g ∈ Y, ∀ b ∈ Bs, g * b * g⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  classical
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSHat p B y K := hnb.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma K hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : K, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom K hN θ b l⟩
  have hcA := card_range_ggGamma_mul_of_sHat hp hS hBN
  have hle : Nat.card (ggGamma K hBN).range ≤ Nat.card γ.range := by
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b, hBBs b.2⟩, rfl⟩
  have h3 : p ^ 3 ≤ Nat.card γ.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact (Nat.le_of_mul_le_mul_right h4 hp.pos).trans hle
  obtain ⟨W, hW1, hW2⟩ := hT K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hK γ.range hA hAI h3 (ggTorusSelfCent_ggGamma hN hSC)
  exact ggTableBNbrInner_of_weyl hcfg hnb hN hW1 hW2 hYN hYK hYn hYp

namespace NbrInnerRest

theorem exists_large_elemAbelian_subset {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I) :
    ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
      p ^ 3 ≤ Nat.card E := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have := Fact.mk hp
  have hS : LargeEvenSHat p B y K := hnb.1
  have hB : IsElemAbelian p B := hS.1.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hBBs.trans hN
  set α : ↥B →* MulAut R := ggBeta K θ hBN with hα
  refine ⟨α.range, ?_, isElemAbelian_range (fun a b => Subtype.ext (IsElemAbelian.comm hB a.2 b.2))
    (fun a => Subtype.ext (by simpa using hB.2 a a.2)) α, ?_⟩
  · rintro _ ⟨b, rfl⟩
    exact hBsI b (hBBs b.2)
  have hker : α.ker ≤ (Subgroup.zpowers y).subgroupOf B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_subgroupOf, ← inf_centralizer_eq_zpowers_of_sHat hS]
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one K θ hK (g := ⟨b, hBN b.2⟩) hb⟩
  have hyB : y ∈ B := hS.2.1
  have hy : Nat.card ((Subgroup.zpowers y).subgroupOf B) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hB.2 y hyB) hS.2.2.1]
  have hk : Nat.card α.ker ≤ p := hy ▸ Subgroup.card_le_of_le hker
  have h1 := Subgroup.card_ker_mul_card_range α
  have h2 : p ^ 4 ≤ Nat.card B := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
  have h3 : p * p ^ 3 ≤ p * Nat.card α.range := by
    rw [← pow_succ']
    exact h2.trans (h1 ▸ Nat.mul_le_mul_right _ hk)
  exact Nat.le_of_mul_le_mul_left h3 hp.pos

end NbrInnerRest

end Config

theorem ggTableBNbrInnerInputOn_of_labelAll_card_lt {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
          Nat.card X < p ^ 3) :
    GGTableBNbrInnerInputOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h p lab hp hp2 hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, hlt⟩
    refine ⟨hs, hna, θ, hPθ, fun _ hBsI => ?_⟩
    obtain ⟨E, hEI, hE, hE3⟩ :=
      NbrInnerRest.exists_large_elemAbelian_subset hcfg hnb hK θ hN hBsI
    exact absurd (hlt hs hna E hEI hE) (not_lt.mpr hE3)
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

theorem ggTableBNbrInnerInputOn_of_labelsSC {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => GGTorusNbrSC p R I) :
    GGTableBNbrInnerInputOn S := by
  intro G _ _ p B Bs x L D J hcfg y K hnb hN P hP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hK, lab, hlab, hraw⟩ := hP
  by_cases hSl : S p lab
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ (h p lab hp hlab hSl _ hraw)⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hPθ⟩, hT⟩
    exact ⟨hs, hna, θ, hPθ, fun _ hBsI Y _ hYN hYK _ hYn hYp =>
      ggTableBNbrInner_of_ggTorusNbrSC hcfg hnb hK θ hN hBsI hT hYN hYK hYn hYp⟩
  · refine ⟨hK, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hPθ⟩
    exact ⟨hs, hna, θ, hPθ, fun hS => absurd hS hSl⟩

end CFSG.StandardType

end
