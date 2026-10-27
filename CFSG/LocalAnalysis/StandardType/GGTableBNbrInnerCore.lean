module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGTorusNbr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ∀ Y : Subgroup (MulAut L'),
          (∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          (∀ n ∈ W, ∀ φ ∈ Y, MulAut.conj n * φ * (MulAut.conj n)⁻¹ ∈ Y) →
          (∀ φ ∈ Y, ∀ a ∈ A, φ * a * φ⁻¹ ∈ A) →
          (∀ φ ∈ Y, ∃ k : ℕ, ∀ a ∈ A, φ ^ p ^ k * a = a * φ ^ p ^ k) →
          ∀ φ ∈ Y, ∀ a ∈ A, φ * a = a * φ

theorem ggTorusNbr_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGTorusNbr p r R' I') : GGTorusNbr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]

theorem exists_ne_one_forall_comm_of_pGroup {M : Type*} [Group M] [Finite M] {p : ℕ}
    [Fact p.Prime] {A Y : Subgroup M} (hAp : IsPGroup p A) (hA1 : Nat.card A ≠ 1)
    (hYA : ∀ φ ∈ Y, ∀ a ∈ A, φ * a * φ⁻¹ ∈ A)
    (hYp : ∀ φ ∈ Y, ∃ k : ℕ, ∀ a ∈ A, φ ^ p ^ k * a = a * φ ^ p ^ k) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ φ ∈ Y, φ * a = a * φ := by
  classical
  let ρ : Y →* Equiv.Perm A :=
    { toFun := fun φ =>
        { toFun := fun a => ⟨φ * a * (φ : M)⁻¹, hYA φ φ.2 a a.2⟩
          invFun := fun a => ⟨(φ : M)⁻¹ * a * φ, by
            simpa using hYA (φ : M)⁻¹ (Y.inv_mem φ.2) a a.2⟩
          left_inv := fun a => Subtype.ext (by simp [mul_assoc])
          right_inv := fun a => Subtype.ext (by simp [mul_assoc]) }
      map_one' := by ext a; simp
      map_mul' := fun φ ψ => by ext a; simp [mul_assoc] }
  have hρ : ∀ (φ : Y) (a : A), ((ρ φ a : A) : M) = φ * a * (φ : M)⁻¹ := fun _ _ => rfl
  have hQp : IsPGroup p ρ.range := by
    rintro ⟨_, φ, rfl⟩
    obtain ⟨k, hk⟩ := hYp φ φ.2
    refine ⟨k, Subtype.ext ?_⟩
    ext a
    change ((ρ φ ^ p ^ k) a : M) = a
    rw [← map_pow, hρ]
    push_cast
    rw [hk a a.2, mul_inv_cancel_right]
  have hpA : p ∣ Nat.card A := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hAp
    rcases n with _ | n
    · exact absurd (by simpa using hn) hA1
    · rw [hn, pow_succ]
      exact dvd_mul_left _ _
  have h1 : (1 : A) ∈ MulAction.fixedPoints ρ.range A := by
    rintro ⟨_, φ, rfl⟩
    apply Subtype.ext
    change ((ρ φ 1 : A) : M) = 1
    rw [hρ]
    simp
  obtain ⟨b, hb, hb1⟩ := hQp.exists_fixed_point_of_prime_dvd_card_of_fixed_point A hpA h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun φ hφ => ?_⟩
  have h := congrArg Subtype.val (hb ⟨ρ ⟨φ, hφ⟩, ⟨φ, hφ⟩, rfl⟩)
  change ((ρ ⟨φ, hφ⟩ b : A) : M) = b at h
  rw [hρ] at h
  calc φ * b = φ * b * φ⁻¹ * φ := by group
    _ = b * φ := by rw [h]

theorem inv_conj_mem_of_conj_mem {M : Type*} [Group M] [Finite M] {Y : Subgroup M} {c : M}
    (h : ∀ φ ∈ Y, c * φ * c⁻¹ ∈ Y) {φ : M} (hφ : φ ∈ Y) : c⁻¹ * φ * c ∈ Y := by
  let f : Y → Y := fun χ => ⟨c * χ * c⁻¹, h χ χ.2⟩
  have hf : Function.Injective f := by
    intro χ₁ χ₂ h12
    apply Subtype.ext
    have h' : c * (χ₁ : M) * c⁻¹ = c * χ₂ * c⁻¹ := congrArg Subtype.val h12
    simpa using h'
  obtain ⟨χ, hχ⟩ := (Finite.injective_iff_surjective.mp hf) ⟨φ, hφ⟩
  have e : φ = c * χ * c⁻¹ := (congrArg Subtype.val hχ).symm
  rw [e]
  simp [mul_assoc]

theorem ggTorusNbr_of_ggTorusIrred {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGTorusIrred p r R I) : GGTorusNbr p r R I := by
  have := Fact.mk hp
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  obtain ⟨W, hW1, hW2, -, -⟩ := h L' ψ hψ hker hperf A hA hAI hr h3
  refine ⟨W, hW1, fun Y hWA hWY hYA hYp => ?_⟩
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

section Config

variable {G : Type} [Group G]

theorem normalizerMonoidHom_mul_ggGamma (K : Subgroup G) {Bs : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (g : Subgroup.normalizer (K : Set G)) (b : Bs)
    (hgb : (g : G) * b * (g : G)⁻¹ ∈ Bs) :
    K.normalizerMonoidHom g * ggGamma K hN b * (K.normalizerMonoidHom g)⁻¹ =
      ggGamma K hN ⟨(g : G) * b * (g : G)⁻¹, hgb⟩ := by
  ext l
  rw [← map_inv]
  simp only [MulAut.mul_apply, ggGamma_coe, normalizerMonoidHom_coe]
  push_cast
  group

theorem normalizerMonoidHom_of_mem (K : Subgroup G) (n : K) :
    K.normalizerMonoidHom ⟨(n : G), Subgroup.le_normalizer n.2⟩ = MulAut.conj n := by
  ext l
  rw [normalizerMonoidHom_coe, MulAut.conj_apply]
  push_cast
  rfl

theorem conj_mul_normalizerMonoidHom (K : Subgroup G) (n : K)
    (g : Subgroup.normalizer (K : Set G)) :
    MulAut.conj n * K.normalizerMonoidHom g * (MulAut.conj n)⁻¹ =
      K.normalizerMonoidHom ⟨(n : G) * g * (n : G)⁻¹,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer n.2) g.2)
          (Subgroup.inv_mem _ (Subgroup.le_normalizer n.2))⟩ := by
  rw [← normalizerMonoidHom_of_mem, ← map_inv, ← map_mul, ← map_mul]
  rfl

variable [Finite G]

theorem card_range_ggGamma_mul_of_sHat {p : ℕ} (hp : p.Prime) {B K : Subgroup G} {y : G}
    (hS : LargeEvenSHat p B y K) (hBN : B ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card (ggGamma K hBN).range * p = Nat.card B := by
  have := Fact.mk hp
  have h1 := card_range_mul_card_ker (ggGamma K hBN)
  have hker : (ggGamma K hBN).ker = (Subgroup.zpowers y).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ggGamma_eq_one_iff,
      ← inf_centralizer_eq_zpowers_of_sHat hS]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  rw [hker] at h1
  have hyB : y ∈ B := hS.2.1
  have h2 : Nat.card ((Subgroup.zpowers y).subgroupOf B) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 y hyB) hS.2.2.1]
  rwa [h2] at h1

theorem ggTableBNbrInner_of_ggTorusNbr {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGTorusNbr p r R I) {Y : Subgroup G}
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
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hS.2.2.2.1
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
  have hr : p ^ r ≤ Nat.card γ.range := by
    have h1 := succ_le_twoLocalRank_of_torusLift hp hKy (hS.1.1.2 y hS.2.1) hS.2.2.1 hK θ hlift
    have h2 : p ^ (r + 1) ≤ Nat.card (ggGamma K hBN).range * p := by
      rw [hcA, hS.1.2.1]
      exact Nat.pow_le_pow_right hp.pos h1
    rw [pow_succ] at h2
    exact (Nat.le_of_mul_le_mul_right h2 hp.pos).trans hle
  have h3 : p ^ 3 ≤ Nat.card γ.range := by
    have h4 := pow_four_le_card_of_bmax hp hS.1 hcfg.1.2.2.2.2.2.1.2.2.2
    rw [← hcA, pow_succ] at h4
    exact (Nat.le_of_mul_le_mul_right h4 hp.pos).trans hle
  obtain ⟨W, hW1, hW2⟩ := hT K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hK γ.range hA hAI hr h3
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

end Config

end CFSG.StandardType

end
