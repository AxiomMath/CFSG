module

public import CFSG.Quasithin.Vol2.Ch3Sec3A6Rho
public import CFSG.Quasithin.Vol2.Ch3Sec3A6Fix
public import CFSG.Quasithin.Vol2.Ch3Sec3P5Quot
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3332

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open A6Coc P5Quot
open scoped IsMulCommutative

namespace Mod32

variable {G : Type} [Group G] {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 6)}

theorem beta_injective {β : ↥(blockU L) →* Multiplicative (AltHeart 6)}
    (hβk : β.ker = (blockZ L).subgroupOf (blockU L)) (hZ : blockZ L = ⊥) :
    Function.Injective β := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h1 : u ∈ β.ker := hu
  rw [hβk, Subgroup.mem_subgroupOf, hZ, Subgroup.mem_bot] at h1
  exact Subtype.ext h1

theorem conj_mem_blockU {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (u : ↥(blockU L)) :
    g * u * g⁻¹ ∈ blockU L :=
  (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU hg) u).mp u.2

theorem eq_blockU_of_inv [Finite G] (hA : IsAltBlockTypeWith L 6 α) (hZ : blockZ L = ⊥)
    (hU16 : Nat.card ↥(blockU L) = 16) {J : Subgroup G} (hJU : J ≤ blockU L)
    (hJL : ∀ ℓ ∈ L, ∀ j ∈ J, ℓ * j * ℓ⁻¹ ∈ J) (hJ : J ≠ ⊥) : J = blockU L := by
  classical
  obtain ⟨hαs, -, β, hβs, hβk, hβe⟩ := hA
  have hβi := beta_injective hβk hZ
  obtain ⟨ℓ, hℓ⟩ := hαs bL
  have hU : ∀ (n : ℕ) (u : ↥(blockU L)), (ℓ : G) ^ n * u * ((ℓ : G) ^ n)⁻¹ ∈ blockU L :=
    fun n u => conj_mem_blockU (Subgroup.le_normalizer (L.pow_mem ℓ.2 n)) u
  have hconj : ∀ (n : ℕ) (u : ↥(blockU L)),
      Multiplicative.toAdd (β ⟨(ℓ : G) ^ n * u * ((ℓ : G) ^ n)⁻¹, hU n u⟩) =
        heartAct 6 (bP ^ n) (Multiplicative.toAdd (β u)) := by
    intro n u
    have h1 := heartAct_eq_of_equivariant hβe (ℓ ^ n) u ⟨_, hU n u⟩ (by
      simp only [Subgroup.coe_pow, Subgroup.coe_inv])
    rw [h1, map_pow, hℓ]
    rfl
  let σ : Equiv.Perm ↥J :=
    { toFun := fun j => ⟨ℓ * j * (ℓ : G)⁻¹, hJL ℓ ℓ.2 j j.2⟩
      invFun := fun j => ⟨(ℓ : G)⁻¹ * j * ℓ, by
        simpa using hJL (ℓ : G)⁻¹ (L.inv_mem ℓ.2) j j.2⟩
      left_inv := fun j => Subtype.ext (by
        show (ℓ : G)⁻¹ * ((ℓ : G) * j * (ℓ : G)⁻¹) * ℓ = j
        group)
      right_inv := fun j => Subtype.ext (by
        show (ℓ : G) * ((ℓ : G)⁻¹ * j * ℓ) * (ℓ : G)⁻¹ = j
        group) }
  have hpow : ∀ (n : ℕ) (j : ↥J),
      (((σ ^ n) j : ↥J) : G) = (ℓ : G) ^ n * j * ((ℓ : G) ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro j; simp
    | succ n ih =>
      intro j
      rw [pow_succ', Equiv.Perm.mul_apply]
      show (ℓ : G) * (((σ ^ n) j : ↥J) : G) * (ℓ : G)⁻¹ = _
      rw [ih, pow_succ']
      group
  have h5 : σ ^ 5 = 1 := by
    refine Equiv.ext fun j => Subtype.ext ?_
    rw [hpow, Equiv.Perm.one_apply]
    have h1 := hconj 5 ⟨j, hJU j.2⟩
    rw [show bP ^ 5 = 1 by decide, heartAct_one] at h1
    exact congrArg Subtype.val (hβi (Multiplicative.toAdd.injective h1))
  have hfix : ∀ j : ↥J, σ j = j → j = 1 := by
    intro j hj
    have hj' : (ℓ : G) * j * (ℓ : G)⁻¹ = j := congrArg Subtype.val hj
    set u : ↥(blockU L) := ⟨j, hJU j.2⟩ with hu
    have h1 := hconj 1 u
    have e : (⟨(ℓ : G) ^ 1 * u * ((ℓ : G) ^ 1)⁻¹, hU 1 u⟩ : ↥(blockU L)) = u :=
      Subtype.ext (by
        show (ℓ : G) ^ 1 * u * ((ℓ : G) ^ 1)⁻¹ = u
        rw [pow_one]
        exact hj')
    rw [e, pow_one] at h1
    have h2 : act bP (eps (Multiplicative.toAdd (β u))) = eps (Multiplicative.toAdd (β u)) := by
      rw [← eps_heartAct, ← h1]
    have h3 : β u = 1 := by
      apply Multiplicative.toAdd.injective
      apply eps_injective
      rw [fix_b _ h2, toAdd_one, map_zero]
    have h4 := hβi (h3.trans (map_one β).symm)
    exact Subtype.ext (show (j : G) = 1 from congrArg Subtype.val h4)
  have : Fintype ↥J := Fintype.ofFinite _
  have hsupp : σ.supportᶜ.card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨1, ?_⟩
    ext j
    simp only [Finset.mem_compl, Equiv.Perm.mem_support, not_not, Finset.mem_singleton]
    constructor
    · exact hfix j
    · rintro rfl
      exact Subtype.ext (by show (ℓ : G) * 1 * (ℓ : G)⁻¹ = 1; group)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 5) (n := 1) (σ := σ)
    (by rw [pow_one]; exact h5)
  rw [hsupp, ← Nat.card_eq_fintype_card] at hmod
  have hJcard : Nat.card ↥J ∣ 2 ^ 4 := by
    have := Subgroup.card_dvd_of_le hJU
    rw [hU16] at this
    exact this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hJcard
  rw [hk'] at hmod
  interval_cases k
  · exact absurd (Subgroup.card_eq_one.mp (hk'.trans (by norm_num))) hJ
  · simp [Nat.ModEq] at hmod
  · simp [Nat.ModEq] at hmod
  · simp [Nat.ModEq] at hmod
  · exact Subgroup.eq_of_le_of_card_ge hJU (le_of_eq (hU16.trans (hk'.trans (by norm_num)).symm))

theorem mem_qL_of_rho [Finite G] (hA : IsAltBlockTypeWith L 6 α)
    {T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT : IsPGroup 2 T) {g : G}
    (hg : g ∈ L ⊔ T) (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (h1 : A6Trans.rho hA ⟨g, hgN⟩ = 1) : g ∈ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  let ρ : ↥(L ⊔ T) →* Equiv.Perm (Fin 6) := (A6Trans.rho hA).comp (Subgroup.inclusion hLTN)
  have hK2 : IsPGroup 2 ↥(ρ.ker.map (L ⊔ T).subtype) := by
    rintro ⟨_, ⟨k', hk', rfl⟩⟩
    obtain ⟨ℓ, hℓ, t, ht, hkt⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp k'.2
    obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
    have ha' : t ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hstep : ∀ n : ℕ, ∃ ℓ' ∈ L, (ℓ * t) ^ n = ℓ' * t ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, L.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨ℓ', hℓ', e⟩ := ih
        refine ⟨ℓ' * (t ^ n * ℓ * (t ^ n)⁻¹), L.mul_mem hℓ' ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht n)) ℓ).mp hℓ
        · rw [pow_succ, e]
          group
    obtain ⟨ℓ', hℓ', e⟩ := hstep (2 ^ a)
    rw [ha', mul_one] at e
    have hkL : (k' : G) ^ 2 ^ a ∈ L := by
      rw [hkt, e]
      exact hℓ'
    have h3 : A6Trans.rho hA ⟨(k' : G) ^ 2 ^ a, Subgroup.le_normalizer hkL⟩ = 1 := by
      have e2 : (⟨(k' : G) ^ 2 ^ a, Subgroup.le_normalizer hkL⟩ :
          ↥(Subgroup.normalizer (L : Set G))) = (Subgroup.inclusion hLTN k') ^ 2 ^ a :=
        Subtype.ext (by simp)
      have hk1 : A6Trans.rho hA (Subgroup.inclusion hLTN k') = 1 := hk'
      rw [e2, map_pow, hk1, one_pow]
    have hα : α ⟨_, hkL⟩ = 1 :=
      Subtype.ext ((A6Trans.rho_of_mem hA ⟨_, hkL⟩).symm.trans h3)
    have hker : (⟨_, hkL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hA.2.1]
      exact hα
    obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hker⟩
    have h4 : ((k' : G) ^ 2 ^ a) ^ 2 ^ b = 1 :=
      congrArg (fun x : ↥(CFSG.pCore 2 ↥L) => ((x : ↥L) : G)) hb
    refine ⟨a + b, Subtype.ext ?_⟩
    show (k' : G) ^ 2 ^ (a + b) = 1
    rw [pow_add, pow_mul]
    exact h4
  have hgK : g ∈ ρ.ker.map (L ⊔ T).subtype := ⟨⟨g, hg⟩, h1, rfl⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_subtype_le _)
    (by
      rw [← Subgroup.comap_subtype,
        Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective]
      infer_instance) hK2 hgK

theorem rho_surjective [Finite G] (hA : IsAltBlockTypeWith L 6 α)
    {T V : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT : IsPGroup 2 T)
    (hVQ : V ≤ pCoreOf 2 (L ⊔ T))
    (hQab : ∀ a ∈ pCoreOf 2 (L ⊔ T), ∀ b ∈ pCoreOf 2 (L ⊔ T), a * b = b * a)
    (hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G))
    (hcard : Nat.card ↥(autOn (L ⊔ T) V) = 720) (σ : Equiv.Perm (Fin 6)) :
    ∃ g : ↥(L ⊔ T),
      A6Trans.rho hA (Subgroup.inclusion (sup_le Subgroup.le_normalizer hTL) g) = σ := by
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  let ρ : ↥(L ⊔ T) →* Equiv.Perm (Fin 6) := (A6Trans.rho hA).comp (Subgroup.inclusion hLTN)
  have hle : ρ.ker ≤ (InternalSec.autOnHom hLTV).ker := by
    intro x hx
    rw [InternalSec.mem_ker_autOnHom, Subgroup.mem_centralizer_iff]
    have hxQ := mem_qL_of_rho hA hTL hT x.2 (hLTN x.2) hx
    intro v hv
    exact hQab _ (hVQ hv) _ hxQ
  have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have h1 : (InternalSec.autOnHom hLTV).ker.index = 720 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (InternalSec.autOnHom_surjective hLTV),
      Subgroup.card_top, hcard]
  have h3 : Nat.card ρ.range ≤ 720 := h720 ▸ Subgroup.card_le_card_group _
  have h4 : 720 ∣ Nat.card ρ.range := by
    rw [← h1, ← Subgroup.index_ker ρ]
    exact Subgroup.index_dvd_of_le hle
  have h5 : Nat.card ρ.range = 720 := le_antisymm h3 (Nat.le_of_dvd Nat.card_pos h4)
  have htop : ρ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h5, h720])
  exact (MonoidHom.range_eq_top.mp htop) σ

theorem realizes [Finite G] (hA : IsAltBlockTypeWith L 6 α)
    (hZ : blockZ L = ⊥) (hU16 : Nat.card ↥(blockU L) = 16) {T : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT : IsPGroup 2 T)
    (hUQ : blockU L ≤ pCoreOf 2 (L ⊔ T)) (hQe : IsElemAbelian 2 (pCoreOf 2 (L ⊔ T)))
    (hQ32 : Nat.card ↥(pCoreOf 2 (L ⊔ T)) = 32)
    (hCQ : ∀ q ∈ pCoreOf 2 (L ⊔ T), (∀ ℓ ∈ L, ℓ * q = q * ℓ) → q = 1)
    (hsurj : ∀ σ : Equiv.Perm (Fin 6), ∃ g : ↥(L ⊔ T),
      A6Trans.rho hA (Subgroup.inclusion (sup_le Subgroup.le_normalizer hTL) g) = σ) :
    ∃ _ : IsMulCommutative ↥(pCoreOf 2 (L ⊔ T)),
      permQuot6Model.Realizes (autOn (L ⊔ T) (pCoreOf 2 (L ⊔ T))) ⊤ ⊥ := by
  classical
  set Q : Subgroup G := pCoreOf 2 (L ⊔ T) with hQdef
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hQ2 : ∀ q ∈ Q, q * q = 1 := fun q hq => (pow_two q).symm.trans (hQe.2 q hq)
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hQN : L ⊔ T ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  obtain ⟨-, -, β, hβs, hβk, hβe⟩ := id hA
  have hβi := beta_injective hβk hZ
  let ρ : ↥(L ⊔ T) →* Equiv.Perm (Fin 6) := (A6Trans.rho hA).comp (Subgroup.inclusion hLTN)
  have hker : ∀ g : ↥(L ⊔ T), ρ g = 1 → (g : G) ∈ Q := fun g h1 =>
    mem_qL_of_rho hA hTL hT g.2 (hLTN g.2) h1
  have hUg : ∀ (g : ↥(L ⊔ T)) (u : ↥(blockU L)), (g : G) * u * (g : G)⁻¹ ∈ blockU L :=
    fun g u => conj_mem_blockU (hLTN g.2) u
  have hheart : ∀ (g : ↥(L ⊔ T)) (u : ↥(blockU L)),
      Multiplicative.toAdd (β ⟨_, hUg g u⟩) = heartAct 6 (ρ g) (Multiplicative.toAdd (β u)) :=
    fun g u => A6Trans.rho_heart hA hβs hβk hβe (Subgroup.inclusion hLTN g) u ⟨_, hUg g u⟩ rfl
  have hidx : ((blockU L).subgroupOf Q).index = 2 := by
    have h2 := Subgroup.relIndex_mul_card (H := blockU L) (K := Q)
    rw [inf_of_le_left hUQ, hU16, hQ32] at h2
    show (blockU L).relIndex Q = 2
    omega
  have hmulU : ∀ x ∈ Q, ∀ y ∈ Q, x ∉ blockU L → y ∉ blockU L → x * y ∈ blockU L := by
    intro x hx y hy hxU hyU
    have h1 := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x, hx⟩ : ↥Q))
      (b := ⟨y, hy⟩)).mpr (by
        simp only [Subgroup.mem_subgroupOf]
        exact iff_of_false hxU hyU)
    exact Subgroup.mem_subgroupOf.mp h1
  obtain ⟨q₀, hq₀Q, hq₀U⟩ : ∃ q₀ ∈ Q, q₀ ∉ blockU L := by
    by_contra hcon
    have hle : Q ≤ blockU L := fun q hq => by
      by_contra hqU
      exact hcon ⟨q, hq, hqU⟩
    have := Subgroup.card_le_of_le hle
    rw [hU16, hQ32] at this
    omega
  have hq₀inv : q₀⁻¹ ∉ blockU L := fun h => hq₀U (by simpa using (blockU L).inv_mem h)
  have hgq₀ : ∀ g : ↥(L ⊔ T), (g : G) * q₀ * (g : G)⁻¹ ∈ Q := fun g =>
    (Subgroup.mem_normalizer_iff.mp (hQN g.2) q₀).mp hq₀Q
  have hgq₀U : ∀ g : ↥(L ⊔ T), (g : G) * q₀ * (g : G)⁻¹ ∉ blockU L := fun g h =>
    hq₀U ((Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hLTN g.2)) q₀).mpr h)
  have hc : ∀ g : ↥(L ⊔ T), (g : G) * q₀ * (g : G)⁻¹ * q₀⁻¹ ∈ blockU L := fun g =>
    hmulU _ (hgq₀ g) _ (Q.inv_mem hq₀Q) (hgq₀U g) hq₀inv
  let δ : ↥(L ⊔ T) → AltHeart 6 := fun g => Multiplicative.toAdd (β ⟨_, hc g⟩)
  have hδ : ∀ g h : ↥(L ⊔ T), δ (g * h) = δ g + heartAct 6 (ρ g) (δ h) := by
    intro g h
    have e : (⟨_, hc (g * h)⟩ : ↥(blockU L)) = ⟨_, hUg g ⟨_, hc h⟩⟩ * ⟨_, hc g⟩ := by
      apply Subtype.ext
      show (g : G) * h * q₀ * ((g : G) * h)⁻¹ * q₀⁻¹ =
        (g : G) * ((h : G) * q₀ * (h : G)⁻¹ * q₀⁻¹) * (g : G)⁻¹ *
          ((g : G) * q₀ * (g : G)⁻¹ * q₀⁻¹)
      group
    show Multiplicative.toAdd (β ⟨_, hc (g * h)⟩) = Multiplicative.toAdd (β ⟨_, hc g⟩) +
      heartAct 6 (ρ g) (Multiplicative.toAdd (β ⟨_, hc h⟩))
    rw [e, map_mul, toAdd_mul, hheart g ⟨_, hc h⟩, add_comm]
  have hδQ : ∀ g : ↥(L ⊔ T), (g : G) ∈ Q → δ g = 0 := by
    intro g hg
    have e : (⟨_, hc g⟩ : ↥(blockU L)) = 1 := Subtype.ext (by
      show (g : G) * q₀ * (g : G)⁻¹ * q₀⁻¹ = 1
      rw [hQab _ hg _ hq₀Q, mul_inv_cancel_right, mul_inv_cancel])
    show Multiplicative.toAdd (β ⟨_, hc g⟩) = 0
    rw [e, map_one]
    rfl
  have hδρ : ∀ g g' : ↥(L ⊔ T), ρ g = ρ g' → δ g = δ g' := by
    intro g g' h
    have hk : ρ (g'⁻¹ * g) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h1 := hδ g' (g'⁻¹ * g)
    rw [mul_inv_cancel_left, hδQ _ (hker _ hk), map_zero, add_zero] at h1
    exact h1
  choose gs hgs using hsurj
  have hgs' : ∀ σ, ρ (gs σ) = σ := hgs
  let δb : Equiv.Perm (Fin 6) → AltHeart 6 := fun σ => δ (gs σ)
  have hδbρ : ∀ g : ↥(L ⊔ T), δ g = δb (ρ g) := fun g => hδρ _ _ (hgs' (ρ g)).symm
  have hδb : ∀ σ τ, δb (σ * τ) = δb σ + heartAct 6 σ (δb τ) := by
    intro σ τ
    show δ (gs (σ * τ)) = δ (gs σ) + heartAct 6 σ (δ (gs τ))
    have e : ρ (gs (σ * τ)) = ρ (gs σ * gs τ) := by rw [map_mul, hgs', hgs', hgs']
    rw [hδρ _ _ e, hδ, hgs']
  have hni : ¬ ∃ u : AltHeart 6, ∀ x : Γ, δb x = u - heartAct 6 (x : Equiv.Perm (Fin 6)) u := by
    rintro ⟨u, hu⟩
    obtain ⟨u', hu'⟩ := hβs (Multiplicative.ofAdd u)
    have hq₁ : q₀ * (u' : G) = 1 := by
      refine hCQ _ (Q.mul_mem hq₀Q (hUQ u'.2)) fun ℓ hℓ => ?_
      let gℓ : ↥(L ⊔ T) := ⟨ℓ, Subgroup.mem_sup_left hℓ⟩
      have hρℓ : ρ gℓ = (α ⟨ℓ, hℓ⟩ : Equiv.Perm (Fin 6)) := A6Trans.rho_of_mem hA ⟨ℓ, hℓ⟩
      have h1 : δ gℓ = u - heartAct 6 (ρ gℓ) u := by
        rw [hδbρ, hρℓ]
        exact hu (α ⟨ℓ, hℓ⟩)
      have h2 : (⟨_, hc gℓ⟩ : ↥(blockU L)) * ⟨_, hUg gℓ u'⟩ = u' := by
        apply hβi
        apply Multiplicative.toAdd.injective
        rw [map_mul, toAdd_mul]
        show δ gℓ + Multiplicative.toAdd (β ⟨_, hUg gℓ u'⟩) = Multiplicative.toAdd (β u')
        rw [hheart, h1, hu', toAdd_ofAdd, sub_add_cancel]
      have h3 : (ℓ * q₀ * ℓ⁻¹ * q₀⁻¹) * (ℓ * u' * ℓ⁻¹) = (u' : G) := congrArg Subtype.val h2
      have hb : ℓ * (u' : G) * ℓ⁻¹ ∈ Q := hUQ (hUg gℓ u')
      have hcomm1 : q₀ * (ℓ * u' * ℓ⁻¹) = (ℓ * u' * ℓ⁻¹) * q₀ := hQab _ hq₀Q _ hb
      have hcomm2 : (u' : G) * q₀ = q₀ * u' := hQab _ (hUQ u'.2) _ hq₀Q
      calc ℓ * (q₀ * u') = (ℓ * q₀ * ℓ⁻¹ * q₀⁻¹) * (q₀ * (ℓ * u' * ℓ⁻¹)) * ℓ := by group
        _ = (ℓ * q₀ * ℓ⁻¹ * q₀⁻¹) * ((ℓ * u' * ℓ⁻¹) * q₀) * ℓ := by rw [hcomm1]
        _ = ((ℓ * q₀ * ℓ⁻¹ * q₀⁻¹) * (ℓ * u' * ℓ⁻¹)) * q₀ * ℓ := by group
        _ = u' * q₀ * ℓ := by rw [h3]
        _ = q₀ * u' * ℓ := by rw [hcomm2]
    apply hq₀U
    rw [eq_inv_of_mul_eq_one_left hq₁]
    exact (blockU L).inv_mem u'.2
  obtain ⟨u₁, hu₁⟩ := a6_cocycle (δ₁ := fun x : Γ => δb x) (δ₂ := fun x : Γ => del0 x)
    (fun x y => hδb x y) (fun x y => del0_mul x y) hni del0_not_inner
  let ε : Equiv.Perm (Fin 6) → AltHeart 6 := fun σ => δb σ - del0 σ - (u₁ - heartAct 6 σ u₁)
  have hε : ∀ σ τ, ε (σ * τ) = ε σ + heartAct 6 σ (ε τ) := by
    intro σ τ
    show δb (σ * τ) - del0 (σ * τ) - (u₁ - heartAct 6 (σ * τ) u₁) =
      (δb σ - del0 σ - (u₁ - heartAct 6 σ u₁)) +
        heartAct 6 σ (δb τ - del0 τ - (u₁ - heartAct 6 τ u₁))
    rw [hδb, del0_mul, heartAct_mul]
    simp only [map_sub]
    abel
  have hε0 : ∀ x ∈ alternatingGroup (Fin 6), ε x = 0 := by
    intro x hx
    show δb x - del0 x - (u₁ - heartAct 6 x u₁) = 0
    rw [sub_eq_zero]
    exact hu₁ ⟨x, hx⟩
  have hδbe : ∀ σ, δb σ = del0 σ + (u₁ - heartAct 6 σ u₁) := by
    intro σ
    have h1 : δb σ - del0 σ - (u₁ - heartAct 6 σ u₁) = 0 := crossed_eq_zero hε hε0 σ
    rw [sub_sub, sub_eq_zero] at h1
    exact h1
  have hq₀q : ∀ q ∈ Q, q ∉ blockU L → q₀⁻¹ * q ∈ blockU L := fun q hq hqU =>
    hmulU _ (Q.inv_mem hq₀Q) _ hq hq₀inv hqU
  let jb : ↥(blockU L) → P5.Vec5 := fun u => j45 (eps (Multiplicative.toAdd (β u)))
  have hjb_mul : ∀ u v : ↥(blockU L), jb (u * v) = jb u + jb v := by
    intro u v
    show j45 (eps (Multiplicative.toAdd (β (u * v)))) =
      j45 (eps (Multiplicative.toAdd (β u))) + j45 (eps (Multiplicative.toAdd (β v)))
    rw [map_mul, toAdd_mul, map_add, j45_add]
  have hjb1 : jb 1 = 0 := by
    have h := hjb_mul 1 1
    rw [mul_one] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  have hjb_eq : ∀ u v : ↥(blockU L), jb u = jb v → u = v := fun u v h =>
    hβi (Multiplicative.toAdd.injective (eps_injective (j45_injective h)))
  have hjb_act : ∀ (g : ↥(L ⊔ T)) (u : ↥(blockU L)),
      jb ⟨_, hUg g u⟩ = P5.act (ρ g) (jb u) := by
    intro g u
    show j45 (eps (Multiplicative.toAdd (β ⟨_, hUg g u⟩))) =
      P5.act (ρ g) (j45 (eps (Multiplicative.toAdd (β u))))
    rw [hheart, eps_heartAct, j45_act]
  let θ : ↥Q → P5.Vec5 := fun q =>
    if hq : (q : G) ∈ blockU L then jb ⟨q, hq⟩ else e0 + j45 (eps u₁) + jb ⟨_, hq₀q q q.2 hq⟩
  have hθpos : ∀ (q : ↥Q) (hq : (q : G) ∈ blockU L), θ q = jb ⟨q, hq⟩ := fun _ hq => dite_eq_left hq
  have hθneg : ∀ (q : ↥Q) (hq : (q : G) ∉ blockU L),
      θ q = e0 + j45 (eps u₁) + jb ⟨q₀⁻¹ * q, hq₀q q q.2 hq⟩ := fun _ hq => dite_eq_right hq
  have hθmul : ∀ q q' : ↥Q, θ (q * q') = θ q + θ q' := by
    intro q q'
    by_cases hq : (q : G) ∈ blockU L <;> by_cases hq' : (q' : G) ∈ blockU L
    · have hqq : ((q * q' : ↥Q) : G) ∈ blockU L := (blockU L).mul_mem hq hq'
      rw [hθpos _ hqq, hθpos _ hq, hθpos _ hq', ← hjb_mul]
      rfl
    · have hqq : ((q * q' : ↥Q) : G) ∉ blockU L := fun h => hq' (by
        have := (blockU L).mul_mem ((blockU L).inv_mem hq) h
        simpa using this)
      rw [hθneg _ hqq, hθpos _ hq, hθneg _ hq']
      have e : (⟨q₀⁻¹ * ((q * q' : ↥Q) : G), hq₀q _ (q * q').2 hqq⟩ : ↥(blockU L)) =
          ⟨q, hq⟩ * ⟨q₀⁻¹ * q', hq₀q _ q'.2 hq'⟩ := by
        apply Subtype.ext
        show q₀⁻¹ * ((q : G) * q') = q * (q₀⁻¹ * q')
        rw [← mul_assoc, hQab _ (Q.inv_mem hq₀Q) _ q.2, mul_assoc]
      rw [e, hjb_mul]
      abel
    · have hqq : ((q * q' : ↥Q) : G) ∉ blockU L := fun h => hq (by
        have := (blockU L).mul_mem h ((blockU L).inv_mem hq')
        simpa using this)
      rw [hθneg _ hqq, hθneg _ hq, hθpos _ hq']
      have e : (⟨q₀⁻¹ * ((q * q' : ↥Q) : G), hq₀q _ (q * q').2 hqq⟩ : ↥(blockU L)) =
          ⟨q₀⁻¹ * q, hq₀q _ q.2 hq⟩ * ⟨q', hq'⟩ := by
        apply Subtype.ext
        show q₀⁻¹ * ((q : G) * q') = q₀⁻¹ * q * q'
        rw [mul_assoc]
      rw [e, hjb_mul]
      abel
    · have hqq : ((q * q' : ↥Q) : G) ∈ blockU L := hmulU _ q.2 _ q'.2 hq hq'
      rw [hθpos _ hqq, hθneg _ hq, hθneg _ hq']
      have e : (⟨((q * q' : ↥Q) : G), hqq⟩ : ↥(blockU L)) =
          ⟨q₀⁻¹ * q, hq₀q _ q.2 hq⟩ * ⟨q₀⁻¹ * q', hq₀q _ q'.2 hq'⟩ := by
        apply Subtype.ext
        show (q : G) * q' = q₀⁻¹ * q * (q₀⁻¹ * q')
        have h1 : q₀⁻¹ * q₀⁻¹ = 1 := by rw [← mul_inv_rev, hQ2 _ hq₀Q, inv_one]
        have h2 : (q : G) * q₀⁻¹ = q₀⁻¹ * q := hQab _ q.2 _ (Q.inv_mem hq₀Q)
        calc (q : G) * q' = q * (q₀⁻¹ * q₀⁻¹) * q' := by rw [h1, mul_one]
          _ = (q * q₀⁻¹) * q₀⁻¹ * q' := by group
          _ = (q₀⁻¹ * q) * q₀⁻¹ * q' := by rw [h2]
          _ = q₀⁻¹ * q * (q₀⁻¹ * q') := by group
      rw [e, hjb_mul]
      funext i
      exact (by decide : ∀ a b c d : ZMod 2, c + d = a + b + c + (a + b + d))
        (e0 i) (j45 (eps u₁) i) _ _
  have hθ1 : θ 1 = 0 := (hθpos 1 (blockU L).one_mem).trans hjb1
  have hθker : ∀ x : ↥Q, θ x = 0 → x = 1 := by
    intro x hx
    by_cases h : (x : G) ∈ blockU L
    · rw [hθpos x h] at hx
      have := hjb_eq _ 1 (hx.trans hjb1.symm)
      exact Subtype.ext (show (x : G) = 1 from congrArg Subtype.val this)
    · rw [hθneg x h] at hx
      exfalso
      have h1 : e0 = j45 (eps u₁ + eps (Multiplicative.toAdd (β ⟨_, hq₀q x x.2 h⟩))) := by
        rw [j45_add]
        exact P5.eq_of_add_eq_zero (by rw [← add_assoc]; exact hx)
      exact j45_ne_e0 _ h1.symm
  have hθinj : Function.Injective θ := by
    intro x y hxy
    have h1 : θ (x * y) = 0 := by rw [hθmul, hxy, P5.add_self]
    have h2 := hθker _ h1
    have hy2 : y * y = 1 := Subtype.ext (hQ2 _ y.2)
    calc x = x * y * y := by rw [mul_assoc, hy2, mul_one]
      _ = y := by rw [h2, one_mul]
  have hθact : ∀ (g : ↥(L ⊔ T)) (q : ↥Q),
      θ ⟨(g : G) * q * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hQN g.2) q).mp q.2⟩ =
        P5.act (ρ g) (θ q) := by
    intro g q
    have hgqQ : (g : G) * q * (g : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hQN g.2) q).mp q.2
    by_cases hq : (q : G) ∈ blockU L
    · have hgq : (g : G) * q * (g : G)⁻¹ ∈ blockU L := hUg g ⟨q, hq⟩
      rw [hθpos ⟨_, hgqQ⟩ hgq, hθpos q hq]
      exact hjb_act g ⟨q, hq⟩
    · have hgq : (g : G) * q * (g : G)⁻¹ ∉ blockU L := fun h =>
        hq ((Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hLTN g.2)) q).mpr h)
      rw [hθneg ⟨_, hgqQ⟩ hgq, hθneg q hq]
      have e : (⟨q₀⁻¹ * ((⟨(g : G) * q * (g : G)⁻¹, hgqQ⟩ : ↥Q) : G), hq₀q _ hgqQ hgq⟩ :
          ↥(blockU L)) =
          ⟨_, hc g⟩ * ⟨_, hUg g ⟨_, hq₀q q q.2 hq⟩⟩ := by
        apply Subtype.ext
        show q₀⁻¹ * ((g : G) * q * (g : G)⁻¹) =
          ((g : G) * q₀ * (g : G)⁻¹ * q₀⁻¹) * ((g : G) * (q₀⁻¹ * q) * (g : G)⁻¹)
        have hcm : (g : G) * q₀ * (g : G)⁻¹ * q₀⁻¹ = q₀⁻¹ * ((g : G) * q₀ * (g : G)⁻¹) :=
          hQab _ (hgq₀ g) _ (Q.inv_mem hq₀Q)
        rw [hcm]
        group
      rw [e, hjb_mul, hjb_act]
      have hδg : jb ⟨_, hc g⟩ =
          (P5.act (ρ g) e0 + e0) + (j45 (eps u₁) + P5.act (ρ g) (j45 (eps u₁))) := by
        show j45 (eps (δ g)) = _
        rw [hδbρ, hδbe, map_add, j45_add, j45_eps_del0, j45_eps_sub]
      rw [hδg, P5.act_add, P5.act_add]
      funext i
      exact (by decide : ∀ a b c d e : ZMod 2, b + c + (a + b + (c + d) + e) = a + d + e)
        (P5.act (ρ g) e0 i) (e0 i) (j45 (eps u₁) i) (P5.act (ρ g) (j45 (eps u₁)) i) _
  let θh : ↥Q →* Multiplicative P5.Vec5 :=
    { toFun := fun q => Multiplicative.ofAdd (θ q)
      map_one' := (congrArg Multiplicative.ofAdd hθ1).trans ofAdd_zero
      map_mul' := fun q q' => (congrArg Multiplicative.ofAdd (hθmul q q')).trans (ofAdd_add _ _) }
  have hθbij : Function.Bijective θh := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨fun x y h => hθinj (Multiplicative.ofAdd.injective h), ?_⟩
    simp only [hQ32, Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card,
      Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  let θe : ↥Q ≃* Multiplicative P5.Vec5 := MulEquiv.ofBijective θh hθbij
  let mσ : Equiv.Perm (Fin 6) → MulAut ↥Q := fun σ =>
    (θe.trans (AddEquiv.toMultiplicative (P5.actAdd σ))).trans θe.symm
  have hmσ : ∀ σ q, θe (mσ σ q) = Multiplicative.ofAdd (P5.act σ (θ q)) := fun σ q =>
    θe.apply_symm_apply _
  have hmσθ : ∀ σ q, θ (mσ σ q) = P5.act σ (θ q) := fun σ q =>
    congrArg Multiplicative.toAdd (hmσ σ q)
  have hmσ_conj : ∀ g : ↥(L ⊔ T), conjAct Q ⟨g, hQN g.2⟩ = mσ (ρ g) := by
    intro g
    refine MulEquiv.ext fun q => θe.injective ?_
    have e : conjAct Q ⟨g, hQN g.2⟩ q = ⟨(g : G) * q * (g : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hQN g.2) q).mp q.2⟩ :=
      Subtype.ext (CFSG.QuasithinUnique.Setup.coe_conjAct_apply _ q)
    rw [e, hmσ]
    show Multiplicative.ofAdd (θ ⟨_, _⟩) = _
    rw [hθact]
  have hmem : ∀ σ, mσ σ ∈ autOn (L ⊔ T) Q := fun σ =>
    (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mpr
      ⟨⟨gs σ, hQN (gs σ).2⟩, (gs σ).2, by rw [hmσ_conj, hgs']⟩
  let π : Equiv.Perm (Fin 6) →* ↥(autOn (L ⊔ T) Q) :=
    { toFun := fun σ => ⟨mσ σ, hmem σ⟩
      map_one' := Subtype.ext (MulEquiv.ext fun q => θe.injective (by
        show θe (mσ 1 q) = θe q
        rw [hmσ, P5.act_one]
        rfl))
      map_mul' := fun σ τ => Subtype.ext (MulEquiv.ext fun q => θe.injective (by
        show θe (mσ (σ * τ) q) = θe (mσ σ (mσ τ q))
        rw [hmσ, hmσ, hmσθ, P5.act_mul])) }
  have hπs : Function.Surjective π := by
    rintro ⟨φ, hφ⟩
    obtain ⟨⟨y, hyN⟩, hy, rfl⟩ := (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mp hφ
    refine ⟨ρ ⟨y, hy⟩, Subtype.ext ?_⟩
    show mσ (ρ ⟨y, hy⟩) = conjAct Q ⟨y, hyN⟩
    rw [← hmσ_conj ⟨y, hy⟩]
  let crdE : PQ ≃* Multiplicative P5.Vec5 :=
    MulEquiv.ofBijective P5Quot.crdHom ⟨P5Quot.crdHom_injective, P5Quot.crdHom_surjective⟩
  let β' : ↥(⊤ : Subgroup ↥Q) →* PQ :=
    (crdE.symm.toMonoidHom.comp θe.toMonoidHom).comp
      (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥Q) ≃* ↥Q).toMonoidHom
  refine ⟨hQe.1, ?_⟩
  unfold FFModel.Realizes FFModel.RealizesVia
  refine ⟨π, hπs, bot_le, le_top, fun _ _ _ => Subgroup.mem_top _, ?_,
    fun _ _ _ => Subgroup.mem_top _, ?_, β', ?_, ?_, ?_⟩
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro γ m hm
    have h1 : G6.permAct 6 γ (G6.allOnes 6) = G6.allOnes 6 :=
      Multiplicative.toAdd.injective (funext fun i => rfl)
    have hle : Subgroup.zpowers (G6.allOnes 6) ≤
        (Subgroup.zpowers (G6.allOnes 6)).comap (G6.permAct 6 γ).toMonoidHom :=
      Subgroup.zpowers_le.mpr (by
        show G6.permAct 6 γ (G6.allOnes 6) ∈ Subgroup.zpowers (G6.allOnes 6)
        rw [h1]
        exact Subgroup.mem_zpowers _)
    exact hle hm
  · intro y
    refine ⟨⟨θe.symm (crdE y), Subgroup.mem_top _⟩, ?_⟩
    show crdE.symm (θe (θe.symm (crdE y))) = y
    rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  · intro u
    rw [Subgroup.mem_bot]
    constructor
    · intro h
      have h2 : crdE.symm (θe (u : ↥Q)) = 1 := h
      rw [← map_one crdE.symm] at h2
      exact θe.injective ((crdE.symm.injective h2).trans (map_one θe).symm)
    · intro h
      show crdE.symm (θe (u : ↥Q)) = 1
      rw [h, map_one, map_one]
  · intro γ u m hu hm h
    apply crdE.injective
    have h1 : crdE (β' u) = crdE (QuotientGroup.mk m) := by rw [h]
    have h2 : crdE (β' u) = θe (u : ↥Q) := crdE.apply_symm_apply _
    have h3 : θ (u : ↥Q) = P5.crd (Multiplicative.toAdd (amb m)) :=
      congrArg Multiplicative.toAdd (h2.symm.trans h1)
    show crdE (crdE.symm (θe (mσ γ (u : ↥Q)))) = P5Quot.crdHom (QuotientGroup.mk ⟨_, hm⟩)
    rw [crdE.apply_symm_apply]
    refine (hmσ γ (u : ↥Q)).trans ?_
    apply Multiplicative.toAdd.injective
    show P5.act γ (θ (u : ↥Q)) = P5.crd (Multiplicative.toAdd (amb ⟨_, hm⟩))
    rw [h3]
    exact P5.act_crd γ _

end Mod32

variable {G : Type} [Group G] [Finite G]

theorem insp3_3_32Mod_holds
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    Insp3_3_32Mod := by
  intro G _ _ T M L D h hA6 hTL hTC ⟨φ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hshort, α, hA⟩ := id hA6
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hQT : qL L T ≤ T := pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hUQ : blockU L ≤ qL L T := (C1.blockU_le_blockQ hshort).trans hOQ
  have hZ : blockZ L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ tC L T := ⟨hQT (hUQ hz.1), hz.2⟩
    rw [hTC] at hz'
    exact hz'
  have hU16 := A6Block.card_blockU_of_blockZ_eq_bot hA6 hZ
  have hQe : IsElemAbelian 2 (qL L T) := by
    have hΦ := h.frattini_qL_le_tC h38 h39 hshort hTL
    rw [hTC] at hΦ
    refine Lem3328.isElemAbelian_of_frattini_eq_bot
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ?_
    rw [eq_bot_iff]
    intro x hx
    have := hΦ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_bot] at this ⊢
    exact Subtype.ext this
  have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hrel := h.relIndex_qL_le_two h38 h39 hA6 hTL
  rw [hTC, sup_bot_eq] at hrel
  have hcardQ : Nat.card ↥(qL L T) = (blockU L).relIndex (qL L T) * 16 := by
    have h2 := Subgroup.relIndex_mul_card (H := blockU L) (K := qL L T)
    rw [inf_of_le_left hUQ, hU16] at h2
    exact h2.symm
  have hQpos : 0 < Nat.card ↥(qL L T) := Nat.card_pos
  have hcard720 : Nat.card ↥(autOn (L ⊔ T) (vPlus L T)) = 720 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    rfl
  have hsurj := Mod32.rho_surjective hA hTL hT2 hVQ hQab hLTV hcard720
  rcases (by omega : (blockU L).relIndex (qL L T) = 1 ∨ (blockU L).relIndex (qL L T) = 2)
    with h1 | h2
  ·
    left
    have hQU : qL L T = blockU L :=
      (Subgroup.eq_of_le_of_card_ge hUQ (le_of_eq (by rw [hcardQ, h1, hU16, one_mul]))).symm
    have hVne : vPlus L T ≠ ⊥ := fun hV => h.not_L_le_centralizer h38 h39 fun x _ =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [hV, Subgroup.coe_bot, Set.mem_singleton_iff] at hy
        rw [hy, one_mul, mul_one]
    have hVL : ∀ ℓ ∈ L, ∀ v ∈ vPlus L T, ℓ * v * ℓ⁻¹ ∈ vPlus L T := fun ℓ hℓ v hv =>
      (Subgroup.mem_normalizer_iff.mp (hLTV (Subgroup.mem_sup_left hℓ)) v).mp hv
    have hVU : vPlus L T = blockU L :=
      Mod32.eq_blockU_of_inv hA hZ hU16 (by rw [← hQU]; exact hVQ) hVL hVne
    refine ⟨hQU.trans hVU.symm, hred.2.1.1, ?_, ?_⟩
    · refine lt_of_le_of_ne bot_le fun h0 => hVne ?_
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : ↥(vPlus L T)) ∈ (⊥ : Subgroup ↥(vPlus L T)) := h0 ▸ Subgroup.mem_top _
      rw [Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
    · intro J hJ _ _
      have hJ'U : J.map (vPlus L T).subtype ≤ blockU L := by
        rw [← hVU]
        exact Subgroup.map_subtype_le J
      have hJ'L : ∀ ℓ ∈ L, ∀ j ∈ J.map (vPlus L T).subtype,
          ℓ * j * ℓ⁻¹ ∈ J.map (vPlus L T).subtype := by
        rintro ℓ hℓ _ ⟨j, hj, rfl⟩
        have hℓN : ℓ ∈ Subgroup.normalizer (vPlus L T : Set G) := hLTV (Subgroup.mem_sup_left hℓ)
        have ha : conjAct (vPlus L T) ⟨ℓ, hℓN⟩ ∈ autOn L (vPlus L T) :=
          (CFSG.QuasithinUnique.Setup.mem_autOn_iff).mpr ⟨⟨ℓ, hℓN⟩, hℓ, rfl⟩
        exact ⟨_, hJ ⟨_, ha⟩ j hj, CFSG.QuasithinUnique.Setup.coe_conjAct_apply _ j⟩
      by_cases hJb : J = ⊥
      · exact Or.inl hJb
      · right
        have hne : J.map (vPlus L T).subtype ≠ ⊥ := fun h0 => hJb (by
          rw [eq_bot_iff]
          intro j hj
          have : (j : G) ∈ J.map (vPlus L T).subtype := ⟨j, hj, rfl⟩
          rw [h0, Subgroup.mem_bot] at this
          exact (Subgroup.mem_bot).mpr (Subtype.ext this))
        have hJU := Mod32.eq_blockU_of_inv hA hZ hU16 hJ'U hJ'L hne
        rw [eq_top_iff]
        intro v _
        have hvU : (v : G) ∈ blockU L := by
          rw [← hVU]
          exact v.2
        rw [← hJU] at hvU
        obtain ⟨j, hj, hjv⟩ := hvU
        exact (Subtype.ext hjv : j = v) ▸ hj
  ·
    right
    have hQ32 : Nat.card ↥(qL L T) = 32 := by omega
    have hCQ : ∀ q ∈ qL L T, (∀ ℓ ∈ L, ℓ * q = q * ℓ) → q = 1 := by
      intro q hq hcomm
      have : q ∈ tC L T := ⟨hQT hq, Subgroup.mem_centralizer_iff.mpr hcomm⟩
      rw [hTC] at this
      exact this
    obtain ⟨inst, hR⟩ := Mod32.realizes hA hZ hU16 hTL hT2 hUQ hQe hQ32 hCQ hsurj
    exact ⟨inst, hQ32.trans (by norm_num), hR⟩

end CFSG.Quasithin.H13
