module

public import CFSG.Quasithin.EmptyFaithful.S151V1
public import CFSG.Quasithin.EmptyFaithful.S151V2
public import CFSG.Quasithin.EmptyFaithful.S151V4
public import CFSG.Quasithin.EmptyFaithful.S151ZB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
open scoped commutatorElement

variable {G : Type} [Group G]

theorem blockQ_le_L (L : Subgroup G) : blockQ L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L

theorem L_le_normalizer_blockQ (L : Subgroup G) : L ≤ Subgroup.normalizer (blockQ L : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L

theorem normalizer_le_normalizer_blockQ (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (blockQ L : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L

theorem s151v_normalizer_le_normalizer_blockU (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (blockU L : Set G) := fun _ hx =>
  normalizer_commutator (normalizer_le_normalizer_blockQ L hx) hx

theorem s151v_L_le_normalizer_blockU (L : Subgroup G) : L ≤ Subgroup.normalizer (blockU L : Set G) :=
  Subgroup.le_normalizer.trans (s151v_normalizer_le_normalizer_blockU L)

theorem s151v_normalizer_le_normalizer_blockZ (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (blockZ L : Set G) := fun _ hx =>
  zb_mem_normalizer_inf (s151v_normalizer_le_normalizer_blockU L hx) (s151v_mem_normalizer_centralizer hx)

theorem s151v_blockU_le_blockQ {L : Subgroup G} (hsh : IsShort2 L) : blockU L ≤ blockQ L :=
  fun _ hx => (hsh.2.2.1.1 hx).1

theorem s151v_blockU_le_L {L : Subgroup G} (hsh : IsShort2 L) : blockU L ≤ L :=
  (s151v_blockU_le_blockQ hsh).trans (blockQ_le_L L)

theorem s151v_blockU_comm {L : Subgroup G} (hsh : IsShort2 L) :
    ∀ a ∈ blockU L, ∀ b ∈ blockU L, a * b = b * a := fun _ ha b hb =>
  (Subgroup.mem_centralizer_iff.mp (hsh.2.2.1.1 ha).2 b (s151v_blockU_le_blockQ hsh hb)).symm

theorem s151v_blockU_sq {L : Subgroup G} (hsh : IsShort2 L) : ∀ a ∈ blockU L, a ^ 2 = 1 :=
  hsh.2.2.1.2

theorem blockQ_comm_blockU {L : Subgroup G} (hsh : IsShort2 L) :
    ∀ q ∈ blockQ L, ∀ a ∈ blockU L, q * a * q⁻¹ = a := fun q hq a ha => by
  have := Subgroup.mem_centralizer_iff.mp (hsh.2.2.1.1 ha).2 q hq
  rw [this]; group

theorem s151v_blockZ_le_blockU (L : Subgroup G) : blockZ L ≤ blockU L := inf_le_left

theorem s151v_blockZ_comm {L : Subgroup G} {z ℓ : G} (hz : z ∈ blockZ L) (hℓ : ℓ ∈ L) : ℓ * z * ℓ⁻¹ = z := by
  have := Subgroup.mem_centralizer_iff.mp hz.2 ℓ hℓ
  rw [this]; group

theorem s151v_not_nine_dvd_card [Finite G] {L : Subgroup G} {e : ↥L →* SLt 3}
    {β : ↥(blockU L) →* Multiplicative (Vt 3)} (hs : LnStr L e β) : ¬ 9 ∣ Nat.card ↥L := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective hs.surj
  rw [hs.ker, card_SLt_three] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  rw [hk] at h1
  rw [← h1]
  intro h
  have hc : Nat.Coprime 9 (2 ^ k * 8) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_right k (by norm_num)) (by norm_num)
  have h2 : 9 ∣ (2 ^ k * 8) * 21 := by
    have : 2 ^ k * 168 = (2 ^ k * 8) * 21 := by ring
    rwa [this] at h
  have := Nat.Coprime.dvd_of_dvd_mul_left hc h2
  norm_num at this

theorem s151v_beta_inj {L : Subgroup G} {e : ↥L →* SLt 3} {β : ↥(blockU L) →* Multiplicative (Vt 3)}
    (hs : LnStr L e β) {a b : G} (ha : a ∈ blockU L) (hb : b ∈ blockU L)
    (hab : β ⟨a, ha⟩ = β ⟨b, hb⟩) : a⁻¹ * b ∈ blockZ L := by
  have h1 : β (⟨a, ha⟩⁻¹ * ⟨b, hb⟩) = 1 := by
    rw [map_mul, map_inv, hab]
    exact inv_mul_cancel _
  have h2 : (⟨a, ha⟩⁻¹ * ⟨b, hb⟩ : ↥(blockU L)) ∈ β.ker := h1
  rw [hs.βker] at h2
  exact h2

theorem s151v_beta_ne_one {L : Subgroup G} {e : ↥L →* SLt 3} {β : ↥(blockU L) →* Multiplicative (Vt 3)}
    (hs : LnStr L e β) {a : G} (ha : a ∈ blockU L) (hne : a ∉ blockZ L) : β ⟨a, ha⟩ ≠ 1 := by
  intro h
  have h2 : (⟨a, ha⟩ : ↥(blockU L)) ∈ β.ker := h
  rw [hs.βker] at h2
  exact hne h2

theorem local_card_le_eight [Finite G] {L E : Subgroup G} {e : ↥L →* SLt 3}
    {β : ↥(blockU L) →* Multiplicative (Vt 3)} (hs : LnStr L e β) (hEU : E ≤ blockU L)
    (hEZ : ∀ a ∈ E, a ∈ blockZ L → a = 1) : Nat.card E ≤ 8 := by
  let f : E → Multiplicative (Vt 3) := fun a => β ⟨a, hEU a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := s151v_beta_inj hs (hEU a.2) (hEU b.2) hab
    have h2 : (a : G)⁻¹ * b ∈ E := E.mul_mem (E.inv_mem a.2) b.2
    have h3 := hEZ _ h2 h1
    apply Subtype.ext
    exact inv_mul_eq_one.mp h3
  have h4 := Nat.card_le_card_of_injective f hf
  have h5 : Nat.card (Multiplicative (Vt 3)) = 8 := by
    rw [Nat.card_eq_fintype_card]
    simp [Vt]
  rw [h5] at h4
  exact h4

theorem local_contra_six [Finite G] {L B A : Subgroup G} {e : ↥L →* SLt 3}
    {β : ↥(blockU L) →* Multiplicative (Vt 3)} (hs : LnStr L e β) (hB : IsSylowTwoOf B L)
    (hAU : A ≤ blockU L) (hAZ : ∀ a ∈ A, a ∈ blockZ L → a = 1) (hA : 2 < Nat.card A)
    (hfix : ∀ ℓ ∈ B, ∀ a ∈ A, ℓ * a * ℓ⁻¹ = a) : False := by
  classical
  have hfin : Fintype A := Fintype.ofFinite A
  rw [Nat.card_eq_fintype_card] at hA
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hA
  obtain ⟨a, b, ha1, hb1, hab⟩ : ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
    by_cases hx : x = 1
    · exact ⟨y, z, fun h => hxy (hx.trans h.symm), fun h => hxz (hx.trans h.symm), hyz⟩
    · by_cases hy : y = 1
      · exact ⟨x, z, hx, fun h => hyz (hy.trans h.symm), hxz⟩
      · exact ⟨x, y, hx, hy, hxy⟩
  have hnz : ∀ c : A, c ≠ 1 → (c : G) ∉ blockZ L := fun c hc hcz =>
    hc (Subtype.ext (hAZ c c.2 hcz))
  let ua : ↥(blockU L) := ⟨a, hAU a.2⟩
  let ub : ↥(blockU L) := ⟨b, hAU b.2⟩
  have hwa : Multiplicative.toAdd (β ua) ≠ 0 := fun h =>
    s151v_beta_ne_one hs (hAU a.2) (hnz a ha1) (toAdd_eq_zero.mp h)
  have hwb : Multiplicative.toAdd (β ub) ≠ 0 := fun h =>
    s151v_beta_ne_one hs (hAU b.2) (hnz b hb1) (toAdd_eq_zero.mp h)
  have hwab : Multiplicative.toAdd (β ua) ≠ Multiplicative.toAdd (β ub) := by
    intro h
    have h1 := s151v_beta_inj hs (hAU a.2) (hAU b.2) (Multiplicative.toAdd.injective h)
    have h2 : (a : G)⁻¹ * b ∈ A := A.mul_mem (A.inv_mem a.2) b.2
    have h3 := hAZ _ h2 h1
    exact hab (Subtype.ext (inv_mul_eq_one.mp h3))
  have hfixv : ∀ (c : A) (ℓ : G) (hℓ : ℓ ∈ B) (u : ↥(blockU L)), (u : G) = c →
      (e ⟨ℓ, hB.1 hℓ⟩ : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (β u)) =
        Multiplicative.toAdd (β u) := by
    intro c ℓ hℓ u hu
    refine (hs.equiv ⟨ℓ, hB.1 hℓ⟩ u u ?_).symm
    change (u : G) = ℓ * (u : G) * ℓ⁻¹
    rw [hu]
    exact (hfix ℓ hℓ c c.2).symm
  have hH : ∀ h ∈ (B.subgroupOf L).map e,
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (β ua)) =
          Multiplicative.toAdd (β ua) ∧
      (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (Multiplicative.toAdd (β ub)) =
          Multiplicative.toAdd (β ub) := by
    intro h hh
    obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hh
    have hℓB : (ℓ : G) ∈ B := hℓ
    exact ⟨hfixv a ℓ hℓB ua rfl, hfixv b ℓ hℓB ub rfl⟩
  have h4 := sl3_fix_two_card _ _ hwa hwb hwab _ hH
  have h8 := sylow_image_card hs.surj hB
  omega

theorem local_x_centralizes_U [Finite G] {L : Subgroup G} {e : ↥L →* SLt 3}
    {β : ↥(blockU L) →* Multiplicative (Vt 3)} (hs : LnStr L e β) (hsh : IsShort2 L)
    (hperf : ⁅L, L⁆ = L) {x : G} (hxN : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    {a b : G} (ha : a ∈ blockU L) (hb : b ∈ blockU L) (hxa : x * a * x⁻¹ = a)
    (hxb : x * b * x⁻¹ = b) (hβa : β ⟨a, ha⟩ ≠ 1) (hβb : β ⟨b, hb⟩ ≠ 1)
    (hβab : β ⟨a, ha⟩ ≠ β ⟨b, hb⟩) : ∀ u ∈ blockU L, x * u * x⁻¹ = u := by
  classical
  have hxU : x ∈ Subgroup.normalizer (blockU L : Set G) := s151v_normalizer_le_normalizer_blockU L hxN
  have hxZ : x ∈ Subgroup.normalizer (blockZ L : Set G) := s151v_normalizer_le_normalizer_blockZ L hxN
  have hconjU : ∀ g ∈ blockU L, x * g * x⁻¹ ∈ blockU L := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp hxU g).mp hg
  have hconjZ : ∀ g ∈ blockZ L, x * g * x⁻¹ ∈ blockZ L := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp hxZ g).mp hg
  let _ : CommGroup ↥(blockU L) := { (inferInstance : Group ↥(blockU L)) with
    mul_comm := fun p q => Subtype.ext (s151v_blockU_comm hsh p p.2 q q.2) }
  let σ : ↥(blockU L) →* ↥(blockU L) :=
    { toFun := fun g => ⟨x * g * x⁻¹, hconjU g g.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun g h => by
        apply Subtype.ext
        change x * ((g : G) * h) * x⁻¹ = (x * g * x⁻¹) * (x * h * x⁻¹)
        group }
  have hσ : ∀ g : ↥(blockU L), ((σ g : ↥(blockU L)) : G) = x * g * x⁻¹ := fun g => rfl
  have hσ3 : ∀ g : ↥(blockU L), σ (σ (σ g)) = g := fun g => by
    apply Subtype.ext
    rw [hσ, hσ, hσ]
    have h3x : x * x * x = 1 := by rw [← pow_three']; exact hx3
    have h1 : x * (x * (x * (g : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * (g : G) * (x * x * x)⁻¹ := by
      group
    rw [h1, h3x]; group
  have hσK : ∀ g : ↥(blockU L), β g = 1 → β (σ g) = 1 := fun g hg => by
    have h1 : g ∈ β.ker := hg
    rw [hs.βker] at h1
    have h2 : σ g ∈ β.ker := by
      rw [hs.βker]
      exact hconjZ _ h1
    exact h2
  have hσa : σ ⟨a, ha⟩ = ⟨a, ha⟩ := Subtype.ext hxa
  have hσb : σ ⟨b, hb⟩ = ⟨b, hb⟩ := Subtype.ext hxb
  have hsq : ∀ g : ↥(blockU L), g * g = 1 := fun g => by
    apply Subtype.ext
    have := s151v_blockU_sq hsh g g.2
    simpa [sq] using this
  have hA : ∀ g : ↥(blockU L), β (σ g) = β g :=
    beta_sigma_eq hsq β σ hσ3 hσK hσa hσb hβa hβb hβab
  have hconjL : ∀ ℓ ∈ L, x * ℓ * x⁻¹ ∈ L := fun ℓ hℓ => (Subgroup.mem_normalizer_iff.mp hxN ℓ).mp hℓ
  have hB : ∀ ℓ : ↥L, ∀ hℓ' : x * (ℓ : G) * x⁻¹ ∈ L, e ⟨x * ℓ * x⁻¹, hℓ'⟩ = e ℓ := by
    intro ℓ hℓ'
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    have hmat : (e ⟨x * ℓ * x⁻¹, hℓ'⟩ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (e ℓ : Matrix _ _ _) := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro w
      obtain ⟨u, hu⟩ := hs.βsurj (Multiplicative.ofAdd w)
      have hv : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (s151v_L_le_normalizer_blockU L ℓ.2) u).mp u.2
      have h1 := hs.equiv ℓ u ⟨ℓ * u * ℓ⁻¹, hv⟩ rfl
      have h2 := hs.equiv ⟨x * ℓ * x⁻¹, hℓ'⟩ (σ u) (σ ⟨ℓ * u * ℓ⁻¹, hv⟩) (by
        change x * ((ℓ : G) * u * (ℓ : G)⁻¹) * x⁻¹ =
          (x * ℓ * x⁻¹) * (x * (u : G) * x⁻¹) * (x * ℓ * x⁻¹)⁻¹
        group)
      rw [hA, hA] at h2
      have hw : Multiplicative.toAdd (β u) = w := by rw [hu]; rfl
      rw [hw] at h1 h2
      simp only [Matrix.toLin'_apply]
      rw [← h2, ← h1]
    exact congrFun (congrFun hmat i) j
  have hC : ∀ c ∈ blockU L, ∀ ℓ ∈ L, x * ⁅c, ℓ⁆ * x⁻¹ = ⁅c, ℓ⁆ := by
    intro c hc ℓ hℓ
    have hz : c⁻¹ * (x * c * x⁻¹) ∈ blockZ L :=
      s151v_beta_inj hs hc (hconjU c hc) (hA ⟨c, hc⟩).symm
    set z := c⁻¹ * (x * c * x⁻¹) with hzdef
    have hxc : x * c * x⁻¹ = c * z := by rw [hzdef]; group
    have hℓ' : x * ℓ * x⁻¹ ∈ L := hconjL ℓ hℓ
    have hκ : (x * ℓ * x⁻¹) * ℓ⁻¹ ∈ blockQ L := by
      have hk : (⟨x * ℓ * x⁻¹, hℓ'⟩ * (⟨ℓ, hℓ⟩ : ↥L)⁻¹ : ↥L) ∈ e.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hB ⟨ℓ, hℓ⟩ hℓ', mul_inv_cancel]
      rw [hs.ker] at hk
      have hk' : (⟨x * ℓ * x⁻¹, hℓ'⟩ * (⟨ℓ, hℓ⟩ : ↥L)⁻¹ : ↥L) ∈ CFSG.Open.pCore 2 ↥L := by
        exact hk
      exact Subgroup.mem_map.mpr ⟨⟨x * ℓ * x⁻¹, hℓ'⟩ * (⟨ℓ, hℓ⟩ : ↥L)⁻¹, hk', rfl⟩
    set κ := (x * ℓ * x⁻¹) * ℓ⁻¹ with hκdef
    have hxℓ : x * ℓ * x⁻¹ = κ * ℓ := by rw [hκdef]; group
    have hzU : z ∈ blockU L := s151v_blockZ_le_blockU L hz
    have hmU : ℓ * c⁻¹ * ℓ⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (s151v_L_le_normalizer_blockU L hℓ) c⁻¹).mp
        (Subgroup.inv_mem _ hc)
    have h1 : ℓ * z⁻¹ * ℓ⁻¹ = z⁻¹ := s151v_blockZ_comm (Subgroup.inv_mem _ hz) hℓ
    have h2 : z * κ * z⁻¹ = κ := by
      have := blockQ_comm_blockU hsh κ hκ z hzU
      have h3 : κ * z = z * κ := by
        calc κ * z = κ * z * κ⁻¹ * κ := by group
          _ = z * κ := by rw [this]
      rw [← h3]; group
    have h3 : κ * (ℓ * c⁻¹ * ℓ⁻¹) * κ⁻¹ = ℓ * c⁻¹ * ℓ⁻¹ := blockQ_comm_blockU hsh κ hκ _ hmU
    calc x * ⁅c, ℓ⁆ * x⁻¹ = ⁅x * c * x⁻¹, x * ℓ * x⁻¹⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅c * z, κ * ℓ⁆ := by rw [hxc, hxℓ]
      _ = c * z * κ * (ℓ * z⁻¹ * ℓ⁻¹) * (ℓ * c⁻¹ * ℓ⁻¹) * κ⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = c * z * κ * z⁻¹ * (ℓ * c⁻¹ * ℓ⁻¹) * κ⁻¹ := by rw [h1]
      _ = c * (z * κ * z⁻¹) * (ℓ * c⁻¹ * ℓ⁻¹) * κ⁻¹ := by group
      _ = c * (κ * (ℓ * c⁻¹ * ℓ⁻¹) * κ⁻¹) := by rw [h2]; group
      _ = c * (ℓ * c⁻¹ * ℓ⁻¹) := by rw [h3]
      _ = ⁅c, ℓ⁆ := by simp only [commutatorElement_def]; group
  have hUL : ⁅blockU L, L⁆ = blockU L :=
    commutator_commutator_perfect hperf (blockQ_le_L L) (L_le_normalizer_blockQ L)
  have hle : ⁅blockU L, L⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.commutator_le]
    intro c hc ℓ hℓ
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := hC c hc ℓ hℓ
    calc h * ⁅c, ℓ⁆ = h * ⁅c, ℓ⁆ * h⁻¹ * h := by group
      _ = ⁅c, ℓ⁆ * h := by rw [this]
  intro u hu
  rw [← hUL] at hu
  have := Subgroup.mem_centralizer_iff.mp (hle hu) x rfl
  calc x * u * x⁻¹ = (x * u) * x⁻¹ := rfl
    _ = (u * x) * x⁻¹ := by rw [this]
    _ = u := by group

end CFSG.Quasithin
