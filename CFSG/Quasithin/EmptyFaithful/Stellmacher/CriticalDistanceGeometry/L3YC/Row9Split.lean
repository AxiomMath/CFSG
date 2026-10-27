module

public import CFSG.Quasithin.Vol2.Ch1ModO2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Stellmacher.CD.L3YC

theorem comm_mul_central {G : Type*} [Group G] (a b m : G) (hm : ∀ g, g * m = m * g) :
    ⁅a * m, b⁆ = ⁅a, b⁆ := by
  have h : m * b = b * m := hm b |>.symm
  simp only [commutatorElement_def]
  calc a * m * b * (a * m)⁻¹ * b⁻¹ = a * (m * b) * m⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * m) * m⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_central_mul {G : Type*} [Group G] (a b m : G) (hm : ∀ g, g * m = m * g) :
    ⁅a, b * m⁆ = ⁅a, b⁆ := by
  have h : a * m = m * a := hm a
  simp only [commutatorElement_def]
  calc a * (b * m) * a⁻¹ * (b * m)⁻¹ = (a * b) * (m * a⁻¹) * m⁻¹ * b⁻¹ := by group
    _ = (a * b) * (a⁻¹ * m) * m⁻¹ * b⁻¹ := by
      have : m * a⁻¹ = a⁻¹ * m := by
        have := hm a⁻¹
        exact this.symm
      rw [this]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem centralizes_of_central_error {Q : Type*} [Group Q] (A : Subgroup Q)
    (hperf : commutator ↥A = ⊤) (c : Q)
    (hc : ∀ x ∈ A, ∃ m ∈ A, (∀ y ∈ A, m * y = y * m) ∧ c * x * c⁻¹ = x * m) :
    ∀ x ∈ A, c * x * c⁻¹ = x := by
  let D : Subgroup ↥A :=
    { carrier := {x | c * (x : Q) * c⁻¹ = x}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, Subgroup.coe_mul] at ha hb ⊢
        calc c * ((a : Q) * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
          _ = a * b := by rw [ha, hb]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq, Subgroup.coe_inv] at ha ⊢
        calc c * (a : Q)⁻¹ * c⁻¹ = (c * a * c⁻¹)⁻¹ := by group
          _ = (a : Q)⁻¹ := by rw [ha] }
  have hcomm : ∀ x y : ↥A, ⁅x, y⁆ ∈ D := by
    intro x y
    obtain ⟨mx, hmx, hmxc, hx⟩ := hc x x.2
    obtain ⟨my, hmy, hmyc, hy⟩ := hc y y.2
    show c * ((⁅x, y⁆ : ↥A) : Q) * c⁻¹ = ((⁅x, y⁆ : ↥A) : Q)
    have e : c * ((⁅x, y⁆ : ↥A) : Q) * c⁻¹ =
        ((c * x * c⁻¹ : Q) * (c * y * c⁻¹ : Q) * (c * x * c⁻¹ : Q)⁻¹ * (c * y * c⁻¹ : Q)⁻¹) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e, hx, hy]
    let mx' : ↥A := ⟨mx, hmx⟩
    let my' : ↥A := ⟨my, hmy⟩
    have h1 : ∀ g : ↥A, g * mx' = mx' * g := fun g => Subtype.ext (hmxc g g.2).symm
    have h2 : ∀ g : ↥A, g * my' = my' * g := fun g => Subtype.ext (hmyc g g.2).symm
    have key : ⁅x * mx', y * my'⁆ = ⁅x, y⁆ :=
      (comm_mul_central x (y * my') mx' h1).trans (comm_central_mul x y my' h2)
    have := congrArg Subtype.val key
    simpa [commutatorElement_def, mx', my'] using this
  intro x hx
  have hall : D = ⊤ := by
    rw [eq_top_iff, ← hperf]
    exact (Subgroup.commutator_le).mpr fun g _ h _ => hcomm g h
  have : (⟨x, hx⟩ : ↥A) ∈ D := by rw [hall]; trivial
  exact this

variable {G : Type} [Group G] [Finite G]

theorem image_pCoreOf_central {H L : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥(modO2Image H L))
    (hn : ¬ IsPGroup 2 (↥(modO2Image H L) ⧸ Subgroup.center ↥(modO2Image H L))) :
    ∀ m ∈ pCoreOf 2 L, ∀ hm : m ∈ H, ∀ y ∈ modO2Image H L,
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨m, hm⟩ * y =
        y * (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨m, hm⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmk
  let M : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) := ((pCoreOf 2 L).subgroupOf H).map mk
  have hML : M ≤ modO2Image H L := by
    refine Subgroup.map_mono fun x hx => ?_
    exact (pCoreOf_le 2 L) hx
  have hM2 : IsPGroup 2 ↥M := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    obtain ⟨n, hn'⟩ := (pCoreOf_isPGroup 2 L) ⟨(x : G), hx⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : (x : G) ^ (2 ^ n) = 1 := congrArg Subtype.val hn'
    have h2 : x ^ (2 ^ n) = 1 := Subtype.ext h1
    show ((y ^ 2 ^ n : ↥M) : ↥H ⧸ CFSG.pCore 2 ↥H) = 1
    rw [Subgroup.coe_pow, ← hxy, ← map_pow, h2, map_one]
  have hnormal : (M.subgroupOf (modO2Image H L)).Normal := by
    refine ⟨fun y hy z => ?_⟩
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨⟨l, hlH⟩, hl, hlz⟩ := z.2
    refine ⟨(⟨l, hlH⟩ * x * ⟨l, hlH⟩⁻¹ : ↥H), ?_, ?_⟩
    · show ((l * (x : G) * l⁻¹ : G)) ∈ pCoreOf 2 L
      have hlN := le_normalizer_pCoreOf 2 L hl
      exact (Subgroup.mem_normalizer_iff.mp hlN (x : G)).mp hx
    · have hz : (z : ↥H ⧸ CFSG.pCore 2 ↥H) = mk ⟨l, hlH⟩ := hlz.symm
      show mk (⟨l, hlH⟩ * x * ⟨l, hlH⟩⁻¹) = (z : ↥H ⧸ CFSG.pCore 2 ↥H) * (y : ↥H ⧸ CFSG.pCore 2 ↥H) *
        (z : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹
      rw [hz, map_mul, map_mul, map_inv, hxy]
      rfl
  let π : ↥(modO2Image H L) →* ↥(modO2Image H L) ⧸ Subgroup.center ↥(modO2Image H L) :=
    QuotientGroup.mk' _
  have hMn : ((M.subgroupOf (modO2Image H L)).map π).Normal :=
    Subgroup.Normal.map hnormal π (QuotientGroup.mk'_surjective _)
  have hsimple : IsSimpleGroup (↥(modO2Image H L) ⧸ Subgroup.center ↥(modO2Image H L)) := hq.2.1
  have := hMn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((M.subgroupOf (modO2Image H L)).map π) with hbot | htop
  · intro m hm hmH y hy
    have hmem : mk ⟨m, hmH⟩ ∈ M := ⟨⟨m, hmH⟩, hm, rfl⟩
    have hmL : mk ⟨m, hmH⟩ ∈ modO2Image H L := hML hmem
    have h1 : π ⟨mk ⟨m, hmH⟩, hmL⟩ ∈ (M.subgroupOf (modO2Image H L)).map π :=
      ⟨⟨mk ⟨m, hmH⟩, hmL⟩, hmem, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have := Subgroup.mem_center_iff.mp h1 ⟨y, hy⟩
    exact congrArg Subtype.val this.symm
  · exfalso
    refine hn fun w => ?_
    have hw : w ∈ (M.subgroupOf (modO2Image H L)).map π := by rw [htop]; trivial
    obtain ⟨u, hu, rfl⟩ := hw
    obtain ⟨k, hk⟩ := hM2 ⟨u.1, hu⟩
    refine ⟨k, ?_⟩
    have h1 : u ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [← map_pow, h1, map_one]

theorem split_bar_quasi {H S L : Subgroup G} (hSH : S ≤ H) (hLH : L ≤ H)
    (hsplit : ∀ s ∈ S, ∃ p ∈ S ⊓ L, ∃ c ∈ S,
      (∀ x ∈ L, ∃ m ∈ pCoreOf 2 L, c * x * c⁻¹ = x * m) ∧ s = p * c)
    (hq : CFSG.IsQuasisimple ↥(modO2Image H L))
    (hn : ¬ IsPGroup 2 (↥(modO2Image H L) ⧸ Subgroup.center ↥(modO2Image H L))) :
    ∀ s ∈ (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      ∃ p ∈ (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⊓ modO2Image H L,
        ∃ c ∈ (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
          (∀ x ∈ modO2Image H L, c * x * c⁻¹ = x) ∧ s = p * c := by
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmk
  rintro _ ⟨s', hs', rfl⟩
  obtain ⟨p, hp, c, hc, hcent, hsp⟩ := hsplit (s' : G) hs'
  have hpH : p ∈ H := hSH hp.1
  have hcH : c ∈ H := hSH hc
  refine ⟨mk ⟨p, hpH⟩, ⟨⟨⟨p, hpH⟩, hp.1, rfl⟩, ⟨⟨p, hpH⟩, hp.2, rfl⟩⟩, mk ⟨c, hcH⟩,
    ⟨⟨c, hcH⟩, hc, rfl⟩, ?_, ?_⟩
  · refine centralizes_of_central_error (modO2Image H L) hq.1.commutator_eq_top (mk ⟨c, hcH⟩) ?_
    rintro _ ⟨x', hx', rfl⟩
    obtain ⟨m, hm, hxm⟩ := hcent (x' : G) hx'
    have hmH : m ∈ H := hLH ((pCoreOf_le 2 L) hm)
    have h2 : (⟨c, hcH⟩ : ↥H) * x' * (⟨c, hcH⟩ : ↥H)⁻¹ = x' * ⟨m, hmH⟩ := Subtype.ext hxm
    refine ⟨mk ⟨m, hmH⟩, ⟨⟨m, hmH⟩, ?_, rfl⟩, ?_, ?_⟩
    · exact (pCoreOf_le 2 L) hm
    · exact image_pCoreOf_central hq hn m hm hmH
    · rw [← map_mul, ← map_inv, ← map_mul, h2, map_mul]
  · have : s' = ⟨p, hpH⟩ * ⟨c, hcH⟩ := Subtype.ext hsp
    rw [this, map_mul]

end Stellmacher.CD.L3YC

end CFSG.Quasithin
