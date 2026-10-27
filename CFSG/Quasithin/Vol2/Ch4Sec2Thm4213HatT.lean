module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Irr
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213KG

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4

@[expose] def HatCoreAt (X : Type) [Group X] (M : Subgroup X) (z : X) : Prop :=
  ∀ (t : X) (U S : Subgroup X), U ≤ M → S ≤ M → t ∈ M →
    (∀ a ∈ U, ∀ b ∈ U, a * b = b * a) → Nat.card U = 64 →
    IsPGroup 2 S → 512 ≤ Nat.card S → U ≤ S → z ∈ U → z ∈ Subgroup.centralizer (S : Set X) →
    z ^ 2 = 1 → z ≠ 1 → t ∈ Subgroup.normalizer (S : Set X) →
    t ∈ Subgroup.normalizer (U : Set X) → t * z * t⁻¹ ≠ z →
    z * (t * z * t⁻¹) * (t ^ 2 * z * (t ^ 2)⁻¹) = 1 →
      ¬ U ≤ pCoreOf 2 (M ⊓ Subgroup.centralizer ({z} : Set X))

@[expose] def HatCoreAmb (X : Type) [Group X] (M : Subgroup X) : Prop := ∀ z : X, HatCoreAt X M z

variable {G : Type} [Group G] [Finite G]

namespace T4213N

omit [Finite G] in
theorem exists_elt_of_isHatA6Block {B : Subgroup G} (h : CFSG.Quasithin.IsHatA6Block B) :
    ∃ y ∈ B, (∀ b ∈ B, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 B) ∧
      y ∉ Subgroup.centralizer (blockU B : Set G) ∧
      y ^ 3 ∈ Subgroup.centralizer (blockU B : Set G) := by
  obtain ⟨-, hhat, -, hcent⟩ := h
  have hmemQ : ∀ x : ↥B, (x : G) ∈ pCoreOf 2 B ↔ (QuotientGroup.mk x : ModO2 B) = 1 := by
    intro x
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_map_iff_mem B.subtype_injective
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ↥(Subgroup.center (ModO2 B)), z₀ ≠ 1 := by
    by_contra hne
    push Not at hne
    have h1 : Nat.card (Subgroup.center (ModO2 B)) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hne a).trans (hne b).symm⟩, ⟨1⟩⟩
    have h2 : Nat.card (Subgroup.center (ModO2 B)) = 3 := hhat.2.1
    omega
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (z₀ : ModO2 B)
  have hz3 : (z₀ : ModO2 B) ^ 3 = 1 := by
    have h1 : z₀ ^ Nat.card (Subgroup.center (ModO2 B)) = 1 := pow_card_eq_one'
    rw [hhat.2.1] at h1
    simpa using congrArg Subtype.val h1
  refine ⟨y, y.2, fun b hb => ?_, fun hyU => ?_, ?_⟩
  · have h1 : ((⟨b, hb⟩ * y * (⟨b, hb⟩ : ↥B)⁻¹ * y⁻¹ : ↥B) : G) ∈ pCoreOf 2 B := by
      rw [hmemQ, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, hy]
      have hc := Subgroup.mem_center_iff.mp z₀.2 (QuotientGroup.mk ⟨b, hb⟩)
      rw [hc]
      group
    simpa using h1
  · have h1 : (y : G) ∈ pCoreOf 2 B := by
      rw [← hcent]
      exact Subgroup.mem_inf.mpr ⟨y.2, hyU⟩
    rw [hmemQ, hy] at h1
    exact hz₀ (Subtype.ext h1)
  · have h1 : ((y ^ 3 : ↥B) : G) ∈ pCoreOf 2 B := by
      rw [hmemQ, QuotientGroup.mk_pow, hy, hz3]
    rw [← hcent] at h1
    simpa using (Subgroup.mem_inf.mp h1).2

theorem hatData_of_isHatA6Block {B S : Subgroup G} (h : CFSG.Quasithin.IsHatA6Block B)
    (hS : IsSylowTwoOf S B) {z : G} (hzU : z ∈ blockU B) (hz1 : z ≠ 1) :
    ∃ t ∈ B, t ∈ Subgroup.normalizer (S : Set G) ∧
      t ∈ Subgroup.normalizer (blockU B : Set G) ∧ t * z * t⁻¹ ≠ z ∧
      z * (t * z * t⁻¹) * (t ^ 2 * z * (t ^ 2)⁻¹) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyB, hyc, hyU, hy3⟩ := exists_elt_of_isHatA6Block h
  have hblk := h
  obtain ⟨hsh, -, -, hcent⟩ := h
  obtain ⟨-, -, ⟨hUQ, -⟩, -, -⟩ := hsh
  have hUc : ∀ a ∈ blockU B, ∀ b ∈ blockU B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hUQ ha)).2 b
      (Subgroup.mem_inf.mp (hUQ hb)).1).symm
  have hBU : B ≤ Subgroup.normalizer (blockU B : Set G) :=
    Subgroup.normalizer_commutator_ge_right _ _
  have hQC : pCoreOf 2 B ≤ Subgroup.centralizer (blockU B : Set G) := by
    rw [← hcent]
    exact inf_le_right
  have hQn : ((pCoreOf 2 B).subgroupOf B).Normal := by
    have h1 : (pCoreOf 2 B).subgroupOf B = CFSG.Open.pCore 2 ↥B :=
      Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
    rw [h1]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  have hQS : pCoreOf 2 B ≤ S :=
    le_of_normal_of_isSylowTwoOf hS (pCoreOf_le 2 B) hQn (pCoreOf_isPGroup 2 B)
  have hyS : y ∈ Subgroup.normalizer (S : Set G) := by
    refine A4.mem_normalizer_of_conj_mem fun s hs => ?_
    have h1 := hyc s⁻¹ (B.inv_mem (hS.1 hs))
    have h2 : y * s * y⁻¹ = s * (s⁻¹ * y * s⁻¹⁻¹ * y⁻¹) := by group
    rw [h2]
    exact S.mul_mem hs (hQS h1)
  set W := blockU B ⊓ Subgroup.centralizer ({y} : Set G) with hWdef
  have hBW : B ≤ Subgroup.normalizer (W : Set G) := by
    intro b hb
    refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
    obtain ⟨hwU, hwy⟩ := Subgroup.mem_inf.mp hw
    have hwy' : y * w = w * y := (Subgroup.mem_centralizer_singleton_iff.mp hwy).symm
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hBU hb) w).mp hwU, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    symm
    have hq := hQC (hyc b⁻¹ (B.inv_mem hb))
    set q := b⁻¹ * y * b⁻¹⁻¹ * y⁻¹ with hq_def
    have hqw : q * w = w * q := (Subgroup.mem_centralizer_iff.mp hq w hwU).symm
    have e1 : b⁻¹ * y * b = q * y := by rw [hq_def]; group
    calc y * (b * w * b⁻¹) = b * ((b⁻¹ * y * b) * w) * b⁻¹ := by group
      _ = b * (q * (y * w)) * b⁻¹ := by rw [e1]; group
      _ = b * (q * (w * y)) * b⁻¹ := by rw [hwy']
      _ = b * ((q * w) * y) * b⁻¹ := by group
      _ = b * ((w * q) * y) * b⁻¹ := by rw [hqw]
      _ = b * (w * (b⁻¹ * y * b)) * b⁻¹ := by rw [e1]; group
      _ = b * w * b⁻¹ * y := by group
  have hW : W = ⊥ := by
    rcases eq_bot_or_eq_blockU_of_isHatA6Block hblk (inf_le_left : W ≤ blockU B) hBW with
      hW | hW
    · exact hW
    · exfalso
      apply hyU
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : u ∈ W := by rw [hWdef, hW]; exact hu
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hu').2
  have hfix : ∀ w ∈ blockU B, y * w * y⁻¹ = w → w = 1 := by
    intro w hw hyw
    have h1 : w ∈ W := by
      refine Subgroup.mem_inf.mpr ⟨hw, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * y = y * w * y⁻¹ * y := by rw [hyw]
        _ = y * w := by group
    rw [hW, Subgroup.mem_bot] at h1
    exact h1
  have hyUN : y ∈ Subgroup.normalizer (blockU B : Set G) := hBU hyB
  have hconj : ∀ w ∈ blockU B, y * w * y⁻¹ ∈ blockU B := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hyUN w).mp hw
  refine ⟨y, hyB, hyS, hyUN, fun h1 => hz1 (hfix z hzU h1), ?_⟩
  have hz1' := hconj z hzU
  have hz2' : y ^ 2 * z * (y ^ 2)⁻¹ ∈ blockU B := by
    have := hconj _ hz1'
    simpa [pow_two, mul_assoc] using this
  have hz3' : y ^ 3 * z * (y ^ 3)⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hy3 z hzU
    calc y ^ 3 * z * (y ^ 3)⁻¹ = z * y ^ 3 * (y ^ 3)⁻¹ := by rw [this]
      _ = z := by group
  apply hfix _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hzU hz1') hz2')
  have e1 : y * (z * (y * z * y⁻¹) * (y ^ 2 * z * (y ^ 2)⁻¹)) * y⁻¹ =
      (y * z * y⁻¹) * (y ^ 2 * z * (y ^ 2)⁻¹) * (y ^ 3 * z * (y ^ 3)⁻¹) := by group
  rw [e1, hz3']
  calc (y * z * y⁻¹) * (y ^ 2 * z * (y ^ 2)⁻¹) * z
      = z * ((y * z * y⁻¹) * (y ^ 2 * z * (y ^ 2)⁻¹)) := by
        rw [hUc _ (Subgroup.mul_mem _ hz1' hz2') z hzU]
    _ = z * (y * z * y⁻¹) * (y ^ 2 * z * (y ^ 2)⁻¹) := by group

theorem card_sylow_ge_of_isHatA6Block {B S : Subgroup G} (h : CFSG.Quasithin.IsHatA6Block B)
    (hS : IsSylowTwoOf S B) : 512 ≤ Nat.card S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hhat, hcard, -⟩ := h
  have hUQ : blockU B ≤ pCoreOf 2 B :=
    commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 B)
  have hQ64 : 64 ∣ Nat.card (pCoreOf 2 B) := by
    have h1 := Subgroup.card_dvd_of_le hUQ
    rw [hcard] at h1
    exact h1
  have hQcard : Nat.card (pCoreOf 2 B) = Nat.card (CFSG.pCore 2 ↥B) := by
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ B.subtype B.subtype_injective).toEquiv.symm
  have hB : Nat.card B = 1080 * Nat.card (CFSG.pCore 2 ↥B) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥B),
      C489.card_of_isHat_alt6 hhat]
  have h512 : 512 ∣ Nat.card B := by
    rw [hB, ← hQcard]
    obtain ⟨k, hk⟩ := hQ64
    rw [hk]
    exact ⟨135 * k, by ring⟩
  have hmul : Nat.card S * S.relIndex B = Nat.card B := by
    have h1 := Subgroup.relIndex_mul_card S B
    rw [inf_eq_left.mpr hS.1] at h1
    rw [mul_comm]
    exact h1
  have hodd : Nat.Coprime 512 (S.relIndex B) := by
    have h2 : ¬ 2 ∣ S.relIndex B := hS.2.2
    have : Nat.Coprime 2 (S.relIndex B) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
    simpa using this.pow_left 9
  have h1 : 512 ∣ Nat.card S * S.relIndex B := hmul ▸ h512
  have h2 := hodd.dvd_of_dvd_mul_right h1
  exact Nat.le_of_dvd Nat.card_pos h2

theorem not_le_pCoreOf_of_hatCore {X : Type} [Group X] [Finite X] {M : Subgroup X}
    {K : Subgroup G} (e : ↥K ≃* ↥M) {z t : G} {U S : Subgroup G}
    (hUK : U ≤ K) (hSK : S ≤ K) (hzK : z ∈ K) (htK : t ∈ K)
    (hX : HatCoreAt X M ((e ⟨z, hzK⟩ : ↥M) : X))
    (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hU : Nat.card U = 64)
    (hS2 : IsPGroup 2 S) (hS : 512 ≤ Nat.card S) (hUS : U ≤ S) (hzU : z ∈ U)
    (hzS : z ∈ Subgroup.centralizer (S : Set G)) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (htS : t ∈ Subgroup.normalizer (S : Set G)) (htU : t ∈ Subgroup.normalizer (U : Set G))
    (htz : t * z * t⁻¹ ≠ z) (hzt : z * (t * z * t⁻¹) * (t ^ 2 * z * (t ^ 2)⁻¹) = 1) :
    ¬ U ≤ pCoreOf 2 (K ⊓ Subgroup.centralizer ({z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hle
  let ι : ↥K →* X := M.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := M.subtype_injective.comp e.injective
  have hιM : ∀ k : ↥K, ι k ∈ M := fun k => (e k).2
  have hsymm : ∀ (x : X) (hx : x ∈ M), ι (e.symm ⟨x, hx⟩) = x := fun x hx => by
    show ((e (e.symm ⟨x, hx⟩) : ↥M) : X) = x
    rw [MulEquiv.apply_symm_apply]
  let im : Subgroup G → Subgroup X := fun A => (A.subgroupOf K).map ι
  have mem_im : ∀ {A : Subgroup G} {x : X}, x ∈ im A ↔
      ∃ hx : x ∈ M, (e.symm ⟨x, hx⟩ : G) ∈ A := by
    intro A x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hιM a, ?_⟩
      have h1 : e.symm ⟨ι a, hιM a⟩ = a := by
        apply e.injective
        rw [MulEquiv.apply_symm_apply]
        rfl
      rw [h1]
      exact Subgroup.mem_subgroupOf.mp ha
    · rintro ⟨hx, hA⟩
      exact ⟨e.symm ⟨x, hx⟩, hA, hsymm x hx⟩
  have im_le : ∀ A : Subgroup G, im A ≤ M := by
    rintro A _ ⟨a, -, rfl⟩
    exact hιM a
  have card_im : ∀ {A : Subgroup G} (hA : A ≤ K), Nat.card (im A) = Nat.card A := by
    intro A hA
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ ι hι).toEquiv.symm,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv]
  have hιmul : ∀ a b : ↥K, ι (a * b) = ι a * ι b := fun a b => map_mul ι a b
  have hιinv : ∀ a : ↥K, ι a⁻¹ = (ι a)⁻¹ := fun a => map_inv ι a
  set z' : X := ι ⟨z, hzK⟩ with hz'
  set t' : X := ι ⟨t, htK⟩ with ht'
  have mk_mem : ∀ {A : Subgroup G} {x : G} (hxK : x ∈ K), x ∈ A → ι ⟨x, hxK⟩ ∈ im A :=
    fun {A x} hxK hx => ⟨⟨x, hxK⟩, hx, rfl⟩
  have elim : ∀ {A : Subgroup G} {x : X}, x ∈ im A → ∃ a : ↥K, (a : G) ∈ A ∧ ι a = x := by
    rintro A x ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  set N := pCoreOf 2 (K ⊓ Subgroup.centralizer ({z} : Set G)) with hNdef
  have hNK : N ≤ K := (pCoreOf_le 2 _).trans inf_le_left
  have hNC : im N ≤ M ⊓ Subgroup.centralizer ({z'} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨hιM a, ?_⟩
    have hxz := Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (pCoreOf_le 2 _ (Subgroup.mem_subgroupOf.mp ha))).2
    rw [Subgroup.mem_centralizer_singleton_iff, hz', ← hιmul, ← hιmul]
    congr 1
    exact Subtype.ext hxz
  have hCN : M ⊓ Subgroup.centralizer ({z'} : Set X) ≤ Subgroup.normalizer (im N : Set X) := by
    intro c hc
    obtain ⟨hcM, hcz⟩ := Subgroup.mem_inf.mp hc
    set k := e.symm ⟨c, hcM⟩ with hk
    have hkc : ι k = c := hsymm c hcM
    have hkz : (k : G) ∈ K ⊓ Subgroup.centralizer ({z} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨k.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hcz
      rw [← hkc, hz', ← hιmul, ← hιmul] at h1
      exact congrArg Subtype.val (hι h1)
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := elim hx
    rw [← hkc, ← hιinv, ← hιmul, ← hιmul]
    refine ⟨k * a * k⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hkz) _).mp ha
  have hN2 : IsPGroup 2 (im N) := by
    have h1 : IsPGroup 2 (N.subgroupOf K) :=
      (pCoreOf_isPGroup 2 _).of_equiv (Subgroup.subgroupOfEquivOfLe hNK).symm
    exact h1.map _
  have hNO : im N ≤ pCoreOf 2 (M ⊓ Subgroup.centralizer ({z'} : Set X)) :=
    le_pCoreOf_of_le_normalizer 2 hNC hCN hN2
  have hz'' : ((e ⟨z, hzK⟩ : ↥M) : X) = ι ⟨z, hzK⟩ := rfl
  apply hX t' (im U) (im S) (im_le U) (im_le S) (hιM _)
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := elim ha
    obtain ⟨b', hb', rfl⟩ := elim hb
    rw [← hιmul, ← hιmul]
    congr 1
    exact Subtype.ext (hUc _ ha' _ hb')
  · rw [card_im hUK, hU]
  · have h1 : IsPGroup 2 (S.subgroupOf K) :=
      hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
    exact h1.map _
  · rw [card_im hSK]
    exact hS
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := elim hx
    exact ⟨a, hUS ha, rfl⟩
  · exact mk_mem hzK hzU
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨a, ha, rfl⟩ := elim hs
    rw [hz'', ← hιmul, ← hιmul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzS _ ha)
  · rw [hz'', ← map_pow]
    have h1 : (⟨z, hzK⟩ : ↥K) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
    rw [h1, map_one]
  · intro h1
    apply hz1
    have h2 : (⟨z, hzK⟩ : ↥K) = 1 := hι (h1.trans (map_one ι).symm)
    exact congrArg Subtype.val h2
  · refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := elim hx
    rw [ht', ← hιinv, ← hιmul, ← hιmul]
    refine ⟨_, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp htS _).mp ha
  · refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := elim hx
    rw [ht', ← hιinv, ← hιmul, ← hιmul]
    refine ⟨_, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp htU _).mp ha
  · intro h1
    apply htz
    rw [hz'', ht', ← hιinv, ← hιmul, ← hιmul] at h1
    exact congrArg Subtype.val (hι h1)
  · rw [hz'', ht', ← map_pow, ← hιinv, ← hιinv, ← hιmul, ← hιmul, ← hιmul, ← hιmul, ← hιmul,
      ← hιmul]
    have h1 : (⟨z, hzK⟩ : ↥K) * (⟨t, htK⟩ * ⟨z, hzK⟩ * (⟨t, htK⟩ : ↥K)⁻¹) *
        ((⟨t, htK⟩ : ↥K) ^ 2 * ⟨z, hzK⟩ * ((⟨t, htK⟩ : ↥K) ^ 2)⁻¹) = 1 :=
      Subtype.ext (by simpa using hzt)
    rw [h1, map_one]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := elim hx
    exact hNO ⟨a, hle ha, rfl⟩

end T4213N

theorem kgHatA6M24He_of {X₁ X₂ : Type} [Group X₁] [Finite X₁] [Group X₂] [Finite X₂]
    {M₁ : Subgroup X₁} {M₂ : Subgroup X₂}
    (e₁ : CFSG.Blueprint.NativeSporadic.Carrier .M24 ≃* ↥M₁)
    (e₂ : CFSG.Blueprint.NativeSporadic.Carrier .He ≃* ↥M₂)
    (hM : HatCoreAmb X₁ M₁) (hH : HatCoreAmb X₂ M₂) : KGHatA6M24He := by
  intro G _ _ K B S hK hBK hblk hS z hz hz2
  obtain ⟨hzU, hzS⟩ := Subgroup.mem_inf.mp hz
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hz2' : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  obtain ⟨t, htB, htS, htU, htz, hzt⟩ := T4213N.hatData_of_isHatA6Block hblk hS hzU hz1
  have hS512 := T4213N.card_sylow_ge_of_isHatA6Block hblk hS
  have hblk' := hblk
  obtain ⟨hsh, -, hcard, -⟩ := hblk'
  obtain ⟨-, -, ⟨hUQ, -⟩, -, -⟩ := hsh
  have hUc : ∀ a ∈ blockU B, ∀ b ∈ blockU B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hUQ ha)).2 b
      (Subgroup.mem_inf.mp (hUQ hb)).1).symm
  have hUB : blockU B ≤ B := by
    have h1 : blockU B ≤ pCoreOf 2 B :=
      commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 B)
    exact h1.trans (pCoreOf_le 2 B)
  have hQS : blockU B ≤ S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQn : ((pCoreOf 2 B).subgroupOf B).Normal := by
      have h1 : (pCoreOf 2 B).subgroupOf B = CFSG.Open.pCore 2 ↥B :=
        Subgroup.comap_map_eq_self_of_injective B.subtype_injective _
      rw [h1]
      exact CFSG.LieType.BorelTits.pCore_normal 2
    have h1 : blockU B ≤ pCoreOf 2 B :=
      commutator_le_left_of_le_normalizer (le_normalizer_pCoreOf 2 B)
    exact h1.trans (le_of_normal_of_isSylowTwoOf hS (pCoreOf_le 2 B) hQn (pCoreOf_isPGroup 2 B))
  rcases hK with hK | hK
  · obtain ⟨e⟩ : Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) := hK
    exact T4213N.not_le_pCoreOf_of_hatCore (e.trans e₁) (hUB.trans hBK) (hS.1.trans hBK)
      (hBK (hUB hzU)) (hBK htB) (hM _) hUc hcard hS.2.1 hS512 hQS hzU hzS hz2' hz1 htS htU htz hzt
  · obtain ⟨e⟩ : Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) := hK
    exact T4213N.not_le_pCoreOf_of_hatCore (e.trans e₂) (hUB.trans hBK) (hS.1.trans hBK)
      (hBK (hUB hzU)) (hBK htB) (hH _) hUc hcard hS.2.1 hS512 hQS hzU hzS hz2' hz1 htS htU htz hzt

end CFSG.Quasithin.H13.Ch4
