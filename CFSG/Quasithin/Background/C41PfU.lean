module

public import CFSG.Quasithin.Background.C41PfT
public import CFSG.Quasithin.Background.C41PfO

public section

namespace CFSG.Quasithin.C41Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits Equiv Equiv.Perm
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem comm_swap_of_mem {R M K : Subgroup G} (hRN : R ≤ Subgroup.normalizer (K : Set G))
    (h1 : SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) {n : ℕ} (hn : 4 ≤ n)
    (α : ↥K →* alternatingGroup (Fin n)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G))
    {σ : Equiv.Perm (Fin n)}
    (hconj : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) =
      autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ⊓
        Subgroup.centralizer (autOn R (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :
          Set (MulAut ↥(omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))))
    {p : G} (hpM : p ∈ M) (hpK : p ∈ K) :
    (α ⟨p, hpK⟩ : Equiv.Perm (Fin n)) * σ = σ * (α ⟨p, hpK⟩ : Equiv.Perm (Fin n)) := by
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hV
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := le_normalizer_omegaOneCenter K R
  have hZ : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hRN htR
  have hpMK : conjAct V ⟨p, hKN hpK⟩ ∈ autOn (M ⊓ K) V := ⟨⟨p, hKN hpK⟩, ⟨hpM, hpK⟩, rfl⟩
  rw [hMK] at hpMK
  have htA : conjAct V ⟨t, htV⟩ ∈ autOn R V := ⟨⟨t, htV⟩, htR, rfl⟩
  have hc1 := Subgroup.mem_centralizer_iff.mp hpMK.2 _ htA
  have htpt : t * p * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htK p).mp hpK
  have hxK : t * p * t⁻¹ * p⁻¹ ∈ K := K.mul_mem htpt (K.inv_mem hpK)
  have hxN : t * p * t⁻¹ * p⁻¹ ∈ Subgroup.normalizer (V : Set G) := hKN hxK
  have hxC : t * p * t⁻¹ * p⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    have e : (⟨t * p * t⁻¹ * p⁻¹, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        (⟨t, htV⟩ : ↥(Subgroup.normalizer (V : Set G))) * ⟨p, hKN hpK⟩ *
          (⟨t, htV⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ *
          (⟨p, hKN hpK⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ := rfl
    refine (conjAct_eq_one_iff' ⟨t * p * t⁻¹ * p⁻¹, hxN⟩).mp ?_
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hc1]
    group
  have h1' : α ⟨t * p * t⁻¹ * p⁻¹, hxK⟩ = 1 :=
    (map_eq_one_iff_mem_centralizer hRN h1 α hα hker hZ _).mpr hxC
  have h2 : α ⟨t * p * t⁻¹, htpt⟩ = α ⟨p, hpK⟩ := by
    have e : (⟨t * p * t⁻¹, htpt⟩ : ↥K) = ⟨t * p * t⁻¹ * p⁻¹, hxK⟩ * ⟨p, hpK⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul, h1', one_mul]
  have h3 := hconj p hpK htpt
  rw [h2] at h3
  calc (α ⟨p, hpK⟩ : Equiv.Perm (Fin n)) * σ =
      σ * (α ⟨p, hpK⟩ : Equiv.Perm (Fin n)) * σ⁻¹ * σ := by rw [← h3]
    _ = σ * (α ⟨p, hpK⟩ : Equiv.Perm (Fin n)) := by group

theorem exists_mem_of_comm_swap {R M K : Subgroup G} (hRN : R ≤ Subgroup.normalizer (K : Set G))
    (h1 : SmithC27.C27One R K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) {n : ℕ} (hn : 4 ≤ n)
    (α : ↥K →* alternatingGroup (Fin n)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) (hO2M : pCoreOf 2 K ≤ M) {t : G} (htR : t ∈ R)
    (htV : t ∈ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G))
    (hRt : autOn R (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) =
      Subgroup.zpowers (conjAct (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ⟨t, htV⟩))
    {σ : Equiv.Perm (Fin n)}
    (hconj : ∀ (k : G) (hk : k ∈ K) (hk' : t * k * t⁻¹ ∈ K),
      ((α ⟨t * k * t⁻¹, hk'⟩ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        σ * (α ⟨k, hk⟩ : Equiv.Perm (Fin n)) * σ⁻¹)
    (hMK : autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) =
      autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) ⊓
        Subgroup.centralizer (autOn R (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :
          Set (MulAut ↥(omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))))
    (g : alternatingGroup (Fin n)) (hg : (g : Equiv.Perm (Fin n)) * σ = σ * g) :
    ∃ k : ↥K, (k : G) ∈ M ∧ α k = g := by
  set V := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hV
  have hKN : K ≤ Subgroup.normalizer (V : Set G) := le_normalizer_omegaOneCenter K R
  have hZ : Subgroup.center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  have hCK : K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K := fun x hx => by
    have h0 := (map_eq_one_iff_mem_centralizer hRN h1 α hα hker hZ ⟨x, hx.1⟩).mpr hx.2
    have hx' : (⟨x, hx.1⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := hker ▸ MonoidHom.mem_ker.mpr h0
    rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
    exact ⟨⟨x, hx.1⟩, hx', rfl⟩
  obtain ⟨k, rfl⟩ := hα g
  refine ⟨k, ?_, rfl⟩
  have htK : t ∈ Subgroup.normalizer (K : Set G) := hRN htR
  have htk : t * k * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htK k).mp k.2
  have hcK : t * k * t⁻¹ * (k : G)⁻¹ ∈ K := K.mul_mem htk (K.inv_mem k.2)
  have hc1 : α ⟨t * k * t⁻¹ * (k : G)⁻¹, hcK⟩ = 1 := by
    have e : (⟨t * k * t⁻¹ * (k : G)⁻¹, hcK⟩ : ↥K) = ⟨t * k * t⁻¹, htk⟩ * k⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_inv, mul_inv_eq_one]
    apply Subtype.ext
    rw [hconj k k.2 htk]
    calc σ * (α ⟨(k : G), k.2⟩ : Equiv.Perm (Fin n)) * σ⁻¹ =
        (α k : Equiv.Perm (Fin n)) * σ * σ⁻¹ := by rw [← hg]
      _ = (α k : Equiv.Perm (Fin n)) := by group
  have hcC : t * k * t⁻¹ * (k : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    (map_eq_one_iff_mem_centralizer hRN h1 α hα hker hZ ⟨_, hcK⟩).mp hc1
  have hkV : (k : G) ∈ Subgroup.normalizer (V : Set G) := hKN k.2
  have hcN : t * k * t⁻¹ * (k : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) := hKN hcK
  have hcomm : conjAct V ⟨t, htV⟩ * conjAct V ⟨k, hkV⟩ =
      conjAct V ⟨k, hkV⟩ * conjAct V ⟨t, htV⟩ := by
    have h0 := (conjAct_eq_one_iff' ⟨_, hcN⟩).mpr hcC
    have e : (⟨t * k * t⁻¹ * (k : G)⁻¹, hcN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        (⟨t, htV⟩ : ↥(Subgroup.normalizer (V : Set G))) * ⟨k, hkV⟩ *
          (⟨t, htV⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ *
          (⟨k, hkV⟩ : ↥(Subgroup.normalizer (V : Set G)))⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h0
    calc conjAct V ⟨t, htV⟩ * conjAct V ⟨k, hkV⟩ =
        conjAct V ⟨t, htV⟩ * conjAct V ⟨k, hkV⟩ * (conjAct V ⟨t, htV⟩)⁻¹ *
          (conjAct V ⟨k, hkV⟩)⁻¹ * (conjAct V ⟨k, hkV⟩ * conjAct V ⟨t, htV⟩) := by group
      _ = conjAct V ⟨k, hkV⟩ * conjAct V ⟨t, htV⟩ := by rw [h0, one_mul]
  have hkA : conjAct V ⟨k, hkV⟩ ∈ autOn K V ⊓
      Subgroup.centralizer (autOn R V : Set (MulAut ↥V)) := by
    refine ⟨⟨⟨k, hkV⟩, k.2, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [hRt] at hy
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left hcomm z).eq)
  rw [← hMK] at hkA
  obtain ⟨y, ⟨hyM, hyK⟩, hye⟩ := hkA
  have h2 : conjAct V (y⁻¹ * ⟨k, hkV⟩) = 1 := by rw [map_mul, map_inv, hye, inv_mul_cancel]
  have h3 : (y : G)⁻¹ * k ∈ Subgroup.centralizer (V : Set G) := by
    simpa using A4.conjAct_eq_one_iff.mp h2
  have h4 : (y : G)⁻¹ * k ∈ pCoreOf 2 K := hCK ⟨K.mul_mem (K.inv_mem hyK) k.2, h3⟩
  have e : (k : G) = y * ((y : G)⁻¹ * k) := by group
  rw [e]
  exact M.mul_mem hyM (hO2M h4)

omit [Finite G] in
theorem map_eq_fix2 {K P : Subgroup G} (hPK : P ≤ K) (hPp : ⁅P, P⁆ = P) {n : ℕ} (hn : 7 ≤ n)
    (α : ↥K →* alternatingGroup (Fin n)) {a b : Fin n} (hab : a ≠ b)
    (hne : (P.subgroupOf K).map α ≠ ⊥)
    (hcomm : ∀ (p : G) (hp : p ∈ K), p ∈ P →
      (α ⟨p, hp⟩ : Equiv.Perm (Fin n)) * swap a b = swap a b * (α ⟨p, hp⟩ : Equiv.Perm (Fin n)))
    (hnorm : ∀ g ∈ AltN.fix2 a b, ∃ k : ↥K, α k = g ∧
      (k : G) ∈ Subgroup.normalizer (P : Set G)) :
    (P.subgroupOf K).map α = AltN.fix2 a b := by
  set X := (P.subgroupOf K).map α with hX
  have hXp : ⁅X, X⁆ = X := by
    rw [hX, ← Subgroup.map_commutator, commutator_subgroupOf hPK hPK, hPp]
  have hXS : X ≤ AltN.fix2 a b := AltN.le_fix2_of_perfect hab (by
    rintro _ ⟨⟨p, hp⟩, hpP, rfl⟩
    exact hcomm p hp hpP) hXp
  have hS : IsSimpleGroup ↥(AltN.fix2 a b) := AltN.isSimpleGroup_fix2 hab hn
  refine le_antisymm hXS ?_
  have hXn : (X.subgroupOf (AltN.fix2 a b)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨k, hk, hkN⟩ := hnorm g g.2
    obtain ⟨⟨p, hpK⟩, hpP, hpe⟩ := hx
    have hkp : (k : G) * p * (k : G)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hkN p).mp hpP
    refine ⟨k * ⟨p, hpK⟩ * k⁻¹, hkp, ?_⟩
    rw [map_mul, map_mul, map_inv, hk, hpe]
    rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (X.subgroupOf (AltN.fix2 a b)) with h | h
  · exfalso
    apply hne
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact eq_bot_iff.mpr fun x hx => h.le_bot ⟨hx, hXS hx⟩
  · exact Subgroup.subgroupOf_eq_top.mp h

omit [Finite G] in
theorem map_eq_one_of_perfect {P : Subgroup G} (hPp : ⁅P, P⁆ = P) {Y : Type*} [Group Y]
    (f : ↥P →* Y) (hf : ∀ x y : ↥P, f x * f y = f y * f x) (x : ↥P) : f x = 1 := by
  have htop : ⁅(⊤ : Subgroup ↥P), (⊤ : Subgroup ↥P)⁆ = (⊤ : Subgroup ↥P) := by
    rw [← Subgroup.subgroupOf_self, commutator_subgroupOf le_rfl le_rfl, hPp]
  have hle : (⊤ : Subgroup ↥P) ≤ f.ker := by
    rw [← htop, Subgroup.commutator_le]
    intro c _ d _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hf c d
  exact hle (Subgroup.mem_top x)

omit [Finite G] in
theorem beta_mem_dHeart {K P : Subgroup G} (hPK : P ≤ K) (hPp : ⁅P, P⁆ = P) {n : ℕ}
    {α : ↥K →* alternatingGroup (Fin n)} {β : ↥(blockU K) →* Multiplicative (AltHeart n)}
    (hβe : ∀ (ℓ : ↥K) (u v : ↥(blockU K)), (v : G) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight n), (QuotientAddGroup.mk x : AltHeart n) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight n (α ℓ : Equiv.Perm (Fin n)) x) : AltHeart n) =
          Multiplicative.toAdd (β v))
    {a b : Fin n} (hfix : ∀ (p : G) (hp : p ∈ K), p ∈ P → α ⟨p, hp⟩ ∈ AltN.fix2 a b)
    {q : G} (hq : q ∈ pCoreOf 2 K) {m : G} (hm : m ∈ P) :
    Multiplicative.toAdd (β ⟨⁅q, m⁆, Subgroup.commutator_mem_commutator hq (hPK hm)⟩) ∈
      AltN.dHeart a b := by
  have hUn : K ≤ Subgroup.normalizer (blockU K : Set G) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := pCoreOf 2 K) (H₂ := K)
  have hmem : ∀ x : ↥P, ⁅q, (x : G)⁆ ∈ blockU K := fun x =>
    Subgroup.commutator_mem_commutator hq (hPK x.2)
  let f : ↥P →* Multiplicative (AltHeart n ⧸ AltN.dHeart a b) :=
    { toFun := fun x => Multiplicative.ofAdd (QuotientAddGroup.mk
        (Multiplicative.toAdd (β ⟨⁅q, (x : G)⁆, hmem x⟩)))
      map_one' := by
        have e : (⟨⁅q, ((1 : ↥P) : G)⁆, hmem 1⟩ : ↥(blockU K)) = 1 := Subtype.ext (by simp)
        simp only [e, map_one, toAdd_one, QuotientAddGroup.mk_zero, ofAdd_zero]
      map_mul' := fun x y => by
        have hxy : (x : G) * ⁅q, (y : G)⁆ * (x : G)⁻¹ ∈ blockU K :=
          (Subgroup.mem_normalizer_iff.mp (hUn (hPK x.2)) _).mp (hmem y)
        have e : (⟨⁅q, ((x * y : ↥P) : G)⁆, hmem (x * y)⟩ : ↥(blockU K)) =
            ⟨⁅q, (x : G)⁆, hmem x⟩ * ⟨_, hxy⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, commutatorElement_def]
          group
        have h2 := AltN.hAct_eq_of_blockType hβe ⟨x, hPK x.2⟩ ⟨⁅q, (y : G)⁆, hmem y⟩ ⟨_, hxy⟩ rfl
        have h3 := AltN.sub_hAct_mem_dHeart (hfix x (hPK x.2) x.2)
          (Multiplicative.toAdd (β ⟨⁅q, (y : G)⁆, hmem y⟩))
        have h4 : (QuotientAddGroup.mk (AltN.hAct n (α ⟨x, hPK x.2⟩ : Equiv.Perm (Fin n))
            (Multiplicative.toAdd (β ⟨⁅q, (y : G)⁆, hmem y⟩))) :
              AltHeart n ⧸ AltN.dHeart a b) =
            QuotientAddGroup.mk (Multiplicative.toAdd (β ⟨⁅q, (y : G)⁆, hmem y⟩)) :=
          (QuotientAddGroup.eq_iff_sub_mem.mpr h3).symm
        show Multiplicative.ofAdd (QuotientAddGroup.mk
            (Multiplicative.toAdd (β ⟨⁅q, ((x * y : ↥P) : G)⁆, hmem (x * y)⟩))) =
          Multiplicative.ofAdd (QuotientAddGroup.mk
            (Multiplicative.toAdd (β ⟨⁅q, (x : G)⁆, hmem x⟩))) *
          Multiplicative.ofAdd (QuotientAddGroup.mk
            (Multiplicative.toAdd (β ⟨⁅q, (y : G)⁆, hmem y⟩)))
        rw [e, map_mul, toAdd_mul, h2, QuotientAddGroup.mk_add, h4, ofAdd_add] }
  have hQc : ∀ c d : Multiplicative (AltHeart n ⧸ AltN.dHeart a b), c * d = d * c := by
    intro c d
    obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd c)
    obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd d)
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_mul, ← hy, ← hz, ← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_add,
      AltN.heart_add_comm]
  have h1 := map_eq_one_of_perfect hPp f (fun x y => hQc _ _) ⟨m, hm⟩
  have h2 : (QuotientAddGroup.mk (Multiplicative.toAdd
      (β ⟨⁅q, m⁆, hmem ⟨m, hm⟩⟩)) : AltHeart n ⧸ AltN.dHeart a b) = 0 := by
    have := congrArg Multiplicative.toAdd h1
    simpa [f] using this
  exact (QuotientAddGroup.eq_zero_iff _).mp h2

omit [Finite G] in
theorem beta_commutator {K : Subgroup G} {n : ℕ} {α : ↥K →* alternatingGroup (Fin n)}
    {β : ↥(blockU K) →* Multiplicative (AltHeart n)}
    (hβe : ∀ (ℓ : ↥K) (u v : ↥(blockU K)), (v : G) = ℓ * u * ℓ⁻¹ →
      ∀ x : ↥(evenWeight n), (QuotientAddGroup.mk x : AltHeart n) = Multiplicative.toAdd (β u) →
        (QuotientAddGroup.mk (permWeight n (α ℓ : Equiv.Perm (Fin n)) x) : AltHeart n) =
          Multiplicative.toAdd (β v))
    {u m : G} (hu : u ∈ blockU K) (hm : m ∈ K) (hc : ⁅u, m⁆ ∈ blockU K) :
    Multiplicative.toAdd (β ⟨⁅u, m⁆, hc⟩) =
      Multiplicative.toAdd (β ⟨u, hu⟩) -
        AltN.hAct n (α ⟨m, hm⟩ : Equiv.Perm (Fin n)) (Multiplicative.toAdd (β ⟨u, hu⟩)) := by
  have hUn : K ≤ Subgroup.normalizer (blockU K : Set G) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := pCoreOf 2 K) (H₂ := K)
  have hmu : m * u * m⁻¹ ∈ blockU K := (Subgroup.mem_normalizer_iff.mp (hUn hm) u).mp hu
  have e : (⟨⁅u, m⁆, hc⟩ : ↥(blockU K)) = ⟨u, hu⟩ * (⟨m * u * m⁻¹, hmu⟩ : ↥(blockU K))⁻¹ := by
    apply Subtype.ext
    show u * m * u⁻¹ * m⁻¹ = u * (m * u * m⁻¹)⁻¹
    group
  rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv,
    ← AltN.hAct_eq_of_blockType hβe ⟨m, hm⟩ ⟨u, hu⟩ ⟨m * u * m⁻¹, hmu⟩ rfl, sub_eq_add_neg]

omit [Finite G] in
theorem irreducible_of_altBlockTypeWith {L : Subgroup G} {m : ℕ} (hm : 4 ≤ m)
    {α : ↥L →* alternatingGroup (Fin m)} (h : IsAltBlockTypeWith L m α) :
    blockZ L < blockU L ∧ ∀ W : Subgroup G, blockZ L ≤ W → W ≤ blockU L →
      L ≤ Subgroup.normalizer (W : Set G) → W = blockZ L ∨ W = blockU L := by
  obtain ⟨hαs, -, β, hβs, hβk, hβe⟩ := h
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hUn : L ≤ Subgroup.normalizer (blockU L : Set G) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := blockQ L) (H₂ := L)
  have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by simp
  constructor
  · refine lt_of_le_of_ne hZU fun hEq => ?_
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (QuotientAddGroup.mk (AltN.pairVec
      (⟨0, by omega⟩ : Fin m) ⟨1, by omega⟩)))
    have hk : u ∈ β.ker := by
      rw [hβk, Subgroup.mem_subgroupOf, hEq]
      exact u.2
    rw [MonoidHom.mem_ker, hu] at hk
    exact AltN.mk_pairVec_ne_zero (by omega) h01 (congrArg Multiplicative.toAdd hk)
  · intro W hZW hWU hWN
    set Y : AddSubgroup (AltHeart m) :=
      Subgroup.toAddSubgroup' ((W.subgroupOf (blockU L)).map β) with hY
    have hYinv : ∀ σ ∈ alternatingGroup (Fin m), ∀ y ∈ Y, AltN.hAct m σ y ∈ Y := by
      intro σ hσ y hy
      obtain ⟨w, hwW, hwe⟩ := hy
      obtain ⟨ℓ, hℓ⟩ := hαs ⟨σ, hσ⟩
      have hv : (ℓ : G) * w * (ℓ : G)⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (hUn ℓ.2) w).mp w.2
      have hvW : (ℓ : G) * w * (ℓ : G)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWN ℓ.2) w).mp hwW
      refine ⟨⟨_, hv⟩, hvW, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [AltN.hAct_eq_of_blockType hβe ℓ w ⟨_, hv⟩ rfl, hwe, hℓ]
      rfl
    rcases AltN.heart_irreducible hm Y hYinv with hY0 | hY0
    · left
      refine le_antisymm (fun w hw => ?_) hZW
      have hwU := hWU hw
      have hy : Multiplicative.toAdd (β ⟨w, hwU⟩) ∈ Y := ⟨⟨w, hwU⟩, hw, rfl⟩
      rw [hY0, AddSubgroup.mem_bot] at hy
      have hk : (⟨w, hwU⟩ : ↥(blockU L)) ∈ β.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Multiplicative.ofAdd hy
      rw [hβk] at hk
      exact hk
    · right
      refine le_antisymm hWU fun u hu => ?_
      have hy : Multiplicative.toAdd (β ⟨u, hu⟩) ∈ Y := hY0 ▸ AddSubgroup.mem_top _
      obtain ⟨w, hwW, hwe⟩ := hy
      have hk : w⁻¹ * ⟨u, hu⟩ ∈ β.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwe]
        exact inv_mul_cancel _
      rw [hβk] at hk
      have e : (u : G) = (w : G) * ((w⁻¹ * ⟨u, hu⟩ : ↥(blockU L)) : G) := by simp
      rw [e]
      exact W.mul_mem hwW (hZW hk)

omit [Finite G] in
theorem isQuasisimple_of_mulEquiv_alt {X : Type*} [Group X] {m : ℕ} (hm : 5 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) : CFSG.IsQuasisimple X := by
  have : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hX : IsSimpleGroup X := e.isSimpleGroup
  refine (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup ?_).1
  by_contra h
  push Not at h
  have hc : Subgroup.center (alternatingGroup (Fin m)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    obtain ⟨y, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, h x y]
  rw [alternatingGroup.center_eq_bot (by simp; omega)] at hc
  exact bot_ne_top hc

theorem commutator_le_of_le_sup {Q P V Z : Subgroup G} (hPp : ⁅P, P⁆ = P)
    (hVN : P ≤ Subgroup.normalizer (V : Set G)) (hZC : Z ≤ Subgroup.centralizer (P : Set G))
    (hVP : V ≤ P) (hUVZ : ⁅Q, P⁆ ≤ V ⊔ Z)
    (hab : ∀ u ∈ ⁅Q, P⁆, ∀ v ∈ ⁅Q, P⁆, u * v = v * u) : ⁅Q, P⁆ ≤ V := by
  set U := ⁅Q, P⁆ with hU
  have hUn : P ≤ Subgroup.normalizer (U : Set G) := Subgroup.normalizer_commutator_ge_right Q P
  have hVZn : V ≤ Subgroup.normalizer (Z : Set G) := fun v hv =>
    Subgroup.mem_normalizer_fintype fun z hz => by
      rw [Subgroup.mem_centralizer_iff.mp (hZC hz) v (hVP hv), mul_inv_cancel_right]
      exact hz
  set V' : Subgroup ↥U := V.subgroupOf U with hV'
  have hV'n : V'.Normal := ⟨fun x hx g => by
    have e : g * x * g⁻¹ = x := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [hab _ g.2 _ x.2, mul_inv_cancel_right]
    rw [e]
    exact hx⟩
  have hconj : ∀ m ∈ P, ∀ c ∈ U, m * c * m⁻¹ * c⁻¹ ∈ V := by
    intro m hm c hc
    have hc' : c ∈ ((V : Set G) * (Z : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right V Z hVZn]
      exact hUVZ hc
    obtain ⟨v, hv, z, hz, rfl⟩ := hc'
    have hzm : m * z = z * m := Subgroup.mem_centralizer_iff.mp (hZC hz) m hm
    have hzm' : z * m⁻¹ = m⁻¹ * z := (Commute.inv_left (show Commute m z from hzm)).eq.symm
    have e : m * (v * z) * m⁻¹ * (v * z)⁻¹ = m * v * m⁻¹ * v⁻¹ := by
      calc m * (v * z) * m⁻¹ * (v * z)⁻¹ = m * v * (z * m⁻¹) * z⁻¹ * v⁻¹ := by group
        _ = m * v * (m⁻¹ * z) * z⁻¹ * v⁻¹ := by rw [hzm']
        _ = m * v * m⁻¹ * v⁻¹ := by group
    rw [e]
    exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVN hm) v).mp hv) (V.inv_mem hv)
  rw [hU, Subgroup.commutator_le]
  intro q hq m hm
  have hmem : ∀ x : ↥P, ⁅q, (x : G)⁆ ∈ U := fun x => Subgroup.commutator_mem_commutator hq x.2
  let f : ↥P →* ↥U ⧸ V' :=
    { toFun := fun x => QuotientGroup.mk (⟨⁅q, (x : G)⁆, hmem x⟩ : ↥U)
      map_one' := by
        have e : (⟨⁅q, ((1 : ↥P) : G)⁆, hmem 1⟩ : ↥U) = 1 := Subtype.ext (by simp)
        rw [e]
        rfl
      map_mul' := fun x y => by
        have hxy : (x : G) * ⁅q, (y : G)⁆ * (x : G)⁻¹ ∈ U :=
          (Subgroup.mem_normalizer_iff.mp (hUn x.2) _).mp (hmem y)
        have e : (⟨⁅q, ((x * y : ↥P) : G)⁆, hmem (x * y)⟩ : ↥U) =
            ⟨⁅q, (x : G)⁆, hmem x⟩ * ⟨_, hxy⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, commutatorElement_def]
          group
        have h2 : (QuotientGroup.mk (⟨_, hxy⟩ : ↥U) : ↥U ⧸ V') =
            QuotientGroup.mk (⟨⁅q, (y : G)⁆, hmem y⟩ : ↥U) := by
          rw [QuotientGroup.eq]
          show ((⟨_, hxy⟩ : ↥U)⁻¹ * ⟨⁅q, (y : G)⁆, hmem y⟩ : ↥U) ∈ V'
          rw [Subgroup.mem_subgroupOf]
          have h3 := hconj _ x.2 _ (hmem y)
          have h4 : ((⟨_, hxy⟩ : ↥U)⁻¹ * ⟨⁅q, (y : G)⁆, hmem y⟩ : ↥U) =
              (⟨⁅q, (y : G)⁆, hmem y⟩ : ↥U) * (⟨_, hxy⟩ : ↥U)⁻¹ :=
            Subtype.ext (hab _ (Subgroup.inv_mem _ hxy) _ (hmem y))
          rw [h4]
          have h5 := V.inv_mem h3
          convert h5 using 1
          simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
          group
        show (QuotientGroup.mk (⟨⁅q, ((x * y : ↥P) : G)⁆, hmem (x * y)⟩ : ↥U) : ↥U ⧸ V') =
          QuotientGroup.mk (⟨⁅q, (x : G)⁆, hmem x⟩ : ↥U) *
            QuotientGroup.mk (⟨⁅q, (y : G)⁆, hmem y⟩ : ↥U)
        rw [e, QuotientGroup.mk_mul, h2] }
  have hcomm : ∀ c d : ↥U ⧸ V', c * d = d * c := by
    intro c d
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective d
    have hcd : c * d = d * c := Subtype.ext (hab _ c.2 _ d.2)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcd]
  have h1 := map_eq_one_of_perfect hPp f (fun c d => hcomm _ _) ⟨m, hm⟩
  have h2 : (⟨⁅q, m⁆, hmem ⟨m, hm⟩⟩ : ↥U) ∈ V' := (QuotientGroup.eq_one_iff _).mp h1
  exact h2

section Restrict

variable {K P : Subgroup G} (hPK : P ≤ K) {n : ℕ} (α : ↥K →* alternatingGroup (Fin n))
  {a b : Fin n} (hab : a ≠ b)
  (hfix : ∀ (p : G) (hp : p ∈ K), p ∈ P → α ⟨p, hp⟩ ∈ AltN.fix2 a b)

omit [Finite G] in
@[expose] noncomputable def alphaFix : ↥P →* ↥(AltN.fix2 a b) :=
  (α.comp (Subgroup.inclusion hPK)).codRestrict (AltN.fix2 a b) fun p => hfix p (hPK p.2) p.2

omit [Finite G] in
@[expose] noncomputable def alphaRes : ↥P →* alternatingGroup (Fin (n - 2)) :=
  (AltN.resHom hab).comp (alphaFix hPK α hfix)

omit [Finite G] in
theorem alphaRes_eq_one_iff (hker : α.ker = CFSG.pCore 2 ↥K) (p : ↥P) :
    alphaRes hPK α hab hfix p = 1 ↔ (p : G) ∈ pCoreOf 2 K := by
  rw [alphaRes, MonoidHom.comp_apply, (AltN.resHom_injective hab).eq_iff' (map_one _),
    C2A3Orbits.pCoreOf_eq_map_pCore K, ← hker]
  constructor
  · intro h
    exact ⟨⟨p, hPK p.2⟩, congrArg Subtype.val h, rfl⟩
  · rintro ⟨k, hk, hke⟩
    have : k = ⟨p, hPK p.2⟩ := Subtype.ext hke
    subst this
    exact Subtype.ext hk

omit [Finite G] in
theorem alphaRes_surjective
    (hsurj : ∀ g ∈ AltN.fix2 a b, ∃ (p : G) (hp : p ∈ K), p ∈ P ∧ α ⟨p, hp⟩ = g) :
    Function.Surjective (alphaRes hPK α hab hfix) := by
  intro τ
  obtain ⟨g, rfl⟩ := AltN.resHom_surjective hab τ
  obtain ⟨p, hp, hpP, hpe⟩ := hsurj g g.2
  exact ⟨⟨p, hpP⟩, congrArg (AltN.resHom hab) (Subtype.ext hpe)⟩

theorem ker_alphaRes (hn : 7 ≤ n) (hker : α.ker = CFSG.pCore 2 ↥K)
    (hsurj : ∀ g ∈ AltN.fix2 a b, ∃ (p : G) (hp : p ∈ K), p ∈ P ∧ α ⟨p, hp⟩ = g) :
    (alphaRes hPK α hab hfix).ker = CFSG.pCore 2 ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := alphaRes_surjective hPK α hab hfix hsurj
  refine le_antisymm ?_ ?_
  · have h2 : IsPGroup 2 ↥(alphaRes hPK α hab hfix).ker := by
      intro y
      have hy : ((y : ↥P) : G) ∈ pCoreOf 2 K :=
        (alphaRes_eq_one_iff hPK α hab hfix hker y).mp y.2
      obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨_, hy⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    exact le_sSup ⟨MonoidHom.normal_ker _, h2⟩
  · have : IsSimpleGroup (alternatingGroup (Fin (n - 2))) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have hN : ((CFSG.pCore 2 ↥P).map (alphaRes hPK α hab hfix)).Normal :=
      (CFSG.pCore_normal).map _ hs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((CFSG.pCore 2 ↥P).map (alphaRes hPK α hab hfix)) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have h2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥P).map (alphaRes hPK α hab hfix)) :=
        CFSG.pCore_isPGroup.map _
      rw [h] at h2
      exact AltN.not_isPGroup_two_alt (by omega) (h2.of_equiv Subgroup.topEquiv)

include hPK hab hfix in
theorem pCoreOf_eq_inf (hn : 7 ≤ n) (hker : α.ker = CFSG.pCore 2 ↥K)
    (hsurj : ∀ g ∈ AltN.fix2 a b, ∃ (p : G) (hp : p ∈ K), p ∈ P ∧ α ⟨p, hp⟩ = g) :
    pCoreOf 2 P = P ⊓ pCoreOf 2 K := by
  rw [C2A3Orbits.pCoreOf_eq_map_pCore P, ← ker_alphaRes hPK α hab hfix hn hker hsurj]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (alphaRes_eq_one_iff hPK α hab hfix hker y).mp hy⟩
  · rintro ⟨hxP, hxK⟩
    exact ⟨⟨x, hxP⟩, (alphaRes_eq_one_iff hPK α hab hfix hker ⟨x, hxP⟩).mpr hxK, rfl⟩

theorem isAltBlockTypeWith_alphaRes (hPp : ⁅P, P⁆ = P) (hn : 7 ≤ n)
    (hαw : IsAltBlockTypeWith K n α)
    (hsurj : ∀ g ∈ AltN.fix2 a b, ∃ (p : G) (hp : p ∈ K), p ∈ P ∧ α ⟨p, hp⟩ = g)
    (hUQ : blockU K ≤ pCoreOf 2 K) (hUab : ∀ u ∈ blockU K, ∀ v ∈ blockU K, u * v = v * u)
    (hQN : pCoreOf 2 K ≤ Subgroup.normalizer (P : Set G)) :
    IsAltBlockTypeWith P (n - 2) (alphaRes hPK α hab hfix) := by
  obtain ⟨hαs, hαk, β, hβs, hβk, hβe⟩ := hαw
  have hPO := pCoreOf_eq_inf hPK α hab hfix hn hαk hsurj
  have hQPK : pCoreOf 2 P ≤ pCoreOf 2 K := by
    rw [hPO]
    exact inf_le_right
  have hUU : blockU P ≤ blockU K := Subgroup.commutator_mono hQPK hPK
  have hUn : K ≤ Subgroup.normalizer (blockU K : Set G) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := pCoreOf 2 K) (H₂ := K)
  have hUPn : P ≤ Subgroup.normalizer (blockU P : Set G) :=
    Subgroup.normalizer_commutator_ge_right (H₁ := pCoreOf 2 P) (H₂ := P)
  set α' := alphaRes hPK α hab hfix with hα'
  set i0 : Fin (n - 2) := ⟨0, by omega⟩ with hi0
  set β' : ↥(blockU P) →* Multiplicative (AltHeart (n - 2)) :=
    (AltN.resHeart hab i0).toMultiplicative.comp (β.comp (Subgroup.inclusion hUU)) with hβ'
  have hβ'v : ∀ u : ↥(blockU P), Multiplicative.toAdd (β' u) =
      AltN.resHeart hab i0 (Multiplicative.toAdd (β (Subgroup.inclusion hUU u))) := fun u => rfl
  have hD : ∀ u : ↥(blockU P), ∃ x ∈ AltN.dSub a b, (QuotientAddGroup.mk x : AltHeart n) =
      Multiplicative.toAdd (β (Subgroup.inclusion hUU u)) := by
    set Dp : Subgroup G :=
      ((AddSubgroup.toSubgroup (AltN.dHeart a b)).comap β).map (blockU K).subtype with hDp
    have hle : blockU P ≤ Dp := by
      show ⁅pCoreOf 2 P, P⁆ ≤ Dp
      rw [Subgroup.commutator_le]
      intro q hq m hm
      exact ⟨⟨⁅q, m⁆, Subgroup.commutator_mem_commutator (hQPK hq) (hPK hm)⟩,
        beta_mem_dHeart hPK hPp hβe hfix (hQPK hq) hm, rfl⟩
    intro u
    obtain ⟨y, hy, hye⟩ := hle u.2
    have hyu : y = Subgroup.inclusion hUU u := Subtype.ext hye
    subst hyu
    obtain ⟨x, hx, hxe⟩ := hy
    exact ⟨x, hx, hxe⟩
  have hequiv : ∀ (ℓ : ↥P) (u v : ↥(blockU P)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β' v) =
        AltN.hAct (n - 2) (α' ℓ : Equiv.Perm (Fin (n - 2))) (Multiplicative.toAdd (β' u)) := by
    intro ℓ u v h
    obtain ⟨x, hx, hxe⟩ := hD u
    have hv := AltN.hAct_eq_of_blockType hβe ⟨ℓ, hPK ℓ.2⟩ (Subgroup.inclusion hUU u)
      (Subgroup.inclusion hUU v) h
    rw [hβ'v, hβ'v, hv, ← hxe]
    exact AltN.resHeart_hAct hab i0 (alphaFix hPK α hfix ℓ) hx
  refine ⟨alphaRes_surjective hPK α hab hfix hsurj, ker_alphaRes hPK α hab hfix hn hαk hsurj,
    β', ?_, ?_, fun ℓ u v h y hy => ?_⟩
  ·
    set Y : AddSubgroup (AltHeart (n - 2)) := Subgroup.toAddSubgroup' β'.range with hY
    have hYinv : ∀ σ ∈ alternatingGroup (Fin (n - 2)), ∀ y ∈ Y, AltN.hAct (n - 2) σ y ∈ Y := by
      intro σ hσ y hy
      obtain ⟨u, hu⟩ := hy
      obtain ⟨ℓ, hℓ⟩ := alphaRes_surjective hPK α hab hfix hsurj ⟨σ, hσ⟩
      have hv : (ℓ : G) * u * (ℓ : G)⁻¹ ∈ blockU P :=
        (Subgroup.mem_normalizer_iff.mp (hUPn ℓ.2) u).mp u.2
      refine ⟨⟨_, hv⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [hequiv ℓ u ⟨_, hv⟩ rfl, hu, hℓ]
      rfl
    have hYne : Y ≠ ⊥ := by
      intro hbot
      have h12 : (⟨0, by omega⟩ : Fin (n - 2)) ≠ ⟨1, by omega⟩ := by simp
      have h13 : (⟨0, by omega⟩ : Fin (n - 2)) ≠ ⟨2, by omega⟩ := by simp
      have h23 : (⟨1, by omega⟩ : Fin (n - 2)) ≠ ⟨2, by omega⟩ := by simp
      obtain ⟨g1, hg1, hg1a, -⟩ := AltN.exists_fix2_apply hab (by omega) h12 h23
      obtain ⟨g2, hg2, hg2a, hg2b⟩ := AltN.exists_fix2_apply hab (by omega) h12 h13
      obtain ⟨m1, hm1K, hm1P, hm1⟩ := hsurj g1 hg1
      obtain ⟨m2, hm2K, hm2P, hm2⟩ := hsurj g2 hg2
      obtain ⟨u0, hu0⟩ := hβs (Multiplicative.ofAdd
        (QuotientAddGroup.mk (AltN.pairVec a (AltN.emb hab ⟨0, by omega⟩))))
      have hu0Q : (u0 : G) ∈ pCoreOf 2 K := hUQ u0.2
      have hcU : ⁅(u0 : G), m1⁆ ∈ blockU K := by
        have hmu : m1 * u0 * m1⁻¹ ∈ blockU K :=
          (Subgroup.mem_normalizer_iff.mp (hUn hm1K) u0).mp u0.2
        have e : ⁅(u0 : G), m1⁆ = u0 * (m1 * u0 * m1⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact (blockU K).mul_mem u0.2 ((blockU K).inv_mem hmu)
      have hcP : ⁅(u0 : G), m1⁆ ∈ P := by
        have h1 : (u0 : G) * m1 * (u0 : G)⁻¹ ∈ P :=
          (Subgroup.mem_normalizer_iff.mp (hQN hu0Q) m1).mp hm1P
        rw [commutatorElement_def]
        exact P.mul_mem h1 (P.inv_mem hm1P)
      have hcO : ⁅(u0 : G), m1⁆ ∈ pCoreOf 2 P := by
        rw [hPO]
        exact ⟨hcP, hUQ hcU⟩
      have huP : ⁅⁅(u0 : G), m1⁆, m2⁆ ∈ blockU P := Subgroup.commutator_mem_commutator hcO hm2P
      have hβc := beta_commutator hβe u0.2 hm1K hcU
      have hβu := beta_commutator hβe hcU hm2K (hUU huP)
      have hg1a' : (g1 : Equiv.Perm (Fin n)) a = a := hg1.1
      have hg2a' : (g2 : Equiv.Perm (Fin n)) a = a := hg2.1
      have hval : Multiplicative.toAdd (β (Subgroup.inclusion hUU ⟨_, huP⟩)) =
          QuotientAddGroup.mk (AltN.pairVec (AltN.emb hab ⟨1, by omega⟩)
            (AltN.emb hab ⟨2, by omega⟩)) := by
        rw [show Subgroup.inclusion hUU ⟨_, huP⟩ = ⟨_, hUU huP⟩ from rfl, hβu, hβc, hu0,
          toAdd_ofAdd, AltN.hAct_mk, AltN.permWeight_pairVec, hm1, hg1a', hg1a,
          ← QuotientAddGroup.mk_sub, AltN.pairVec_sub, AltN.hAct_mk, AltN.permWeight_pairVec, hm2,
          hg2a, hg2b, ← QuotientAddGroup.mk_sub, AltN.pairVec_sub]
      have hmem : Multiplicative.toAdd (β' ⟨_, huP⟩) ∈ Y := ⟨⟨_, huP⟩, rfl⟩
      rw [hbot, AddSubgroup.mem_bot, hβ'v, hval, AltN.resHeart_mk, AltN.emb_pairVec] at hmem
      exact AltN.mk_pairVec_ne_zero (by omega) h23 hmem
    rcases AltN.heart_irreducible (by omega) Y hYinv with h | h
    · exact absurd h hYne
    · intro z
      have hz : Multiplicative.toAdd z ∈ Y := h ▸ AddSubgroup.mem_top _
      obtain ⟨u, hu⟩ := hz
      exact ⟨u, hu⟩
  ·
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    obtain ⟨x, hx, hxe⟩ := hD u
    constructor
    · intro h0
      have h0' : AltN.resHeart hab i0 (QuotientAddGroup.mk x) = 0 := by
        have := congrArg Multiplicative.toAdd h0
        rw [hβ'v, ← hxe] at this
        exact this
      have hZK : ∀ m ∈ P, ⁅m, (u : G)⁆ ∈ blockZ K := by
        intro m hmP
        have hm : m ∈ K := hPK hmP
        have hmu : m * u * m⁻¹ ∈ blockU K :=
          (Subgroup.mem_normalizer_iff.mp (hUn hm) u).mp (hUU u.2)
        have hβmu : β ⟨m * u * m⁻¹, hmu⟩ = β (Subgroup.inclusion hUU u) := by
          apply Multiplicative.toAdd.injective
          rw [AltN.hAct_eq_of_blockType hβe ⟨m, hm⟩ (Subgroup.inclusion hUU u) ⟨_, hmu⟩ rfl,
            ← hxe, AltN.hAct_mk,
            AltN.permWeight_eq_of_resHeart_eq_zero hab i0 hx h0' (hfix m hm hmP)]
        have hk : (⟨m * u * m⁻¹, hmu⟩ : ↥(blockU K)) * (Subgroup.inclusion hUU u)⁻¹ ∈ β.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hβmu, mul_inv_cancel]
        rw [hβk] at hk
        have e : ⁅m, (u : G)⁆ =
            (((⟨m * u * m⁻¹, hmu⟩ : ↥(blockU K)) * (Subgroup.inclusion hUU u)⁻¹ :
              ↥(blockU K)) : G) := by
          show m * u * m⁻¹ * (u : G)⁻¹ = m * u * m⁻¹ * (u : G)⁻¹
          rfl
        rw [e]
        exact hk
      let φ : ↥P →* ↥(blockU K) :=
        { toFun := fun m => ⟨⁅(m : G), (u : G)⁆, (hZK m m.2).1⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun m1 m2 => by
            apply Subtype.ext
            show ⁅(m1 : G) * m2, (u : G)⁆ = ⁅(m1 : G), (u : G)⁆ * ⁅(m2 : G), (u : G)⁆
            have hcm : (m1 : G) * ⁅(m2 : G), (u : G)⁆ = ⁅(m2 : G), (u : G)⁆ * m1 :=
              Subgroup.mem_centralizer_iff.mp (hZK m2 m2.2).2 m1 (hPK m1.2)
            calc ⁅(m1 : G) * m2, (u : G)⁆ =
                (m1 : G) * ⁅(m2 : G), (u : G)⁆ * (m1 : G)⁻¹ * ⁅(m1 : G), (u : G)⁆ := by
                  simp only [commutatorElement_def]
                  group
              _ = ⁅(m2 : G), (u : G)⁆ * ⁅(m1 : G), (u : G)⁆ := by
                  rw [hcm]
                  group
              _ = ⁅(m1 : G), (u : G)⁆ * ⁅(m2 : G), (u : G)⁆ :=
                  (hUab _ (hZK m1 m1.2).1 _ (hZK m2 m2.2).1).symm }
      refine ⟨u.2, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
      have h1 := map_eq_one_of_perfect hPp φ
        (fun c d => Subtype.ext (hUab _ (φ c).2 _ (φ d).2)) ⟨m, hm⟩
      have h2 : ⁅m, (u : G)⁆ = 1 := congrArg Subtype.val h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h2
    · rintro ⟨-, hc⟩
      apply Multiplicative.toAdd.injective
      rw [hβ'v, ← hxe, toAdd_one]
      apply AltN.heart_fixed_eq_zero (m := n - 2) (by omega)
      intro τ hτ
      obtain ⟨ℓ, hℓ⟩ := alphaRes_surjective hPK α hab hfix hsurj ⟨τ, hτ⟩
      have h := hequiv ℓ u u (by
        rw [InvMemClass.coe_inv, Subgroup.mem_centralizer_iff.mp hc ℓ ℓ.2, mul_inv_cancel_right])
      rw [hβ'v, ← hxe, hℓ] at h
      exact h.symm
  · rw [hequiv ℓ u v h, ← hy]
    rfl

include hPK hab hfix in
theorem isAltBlockType_of_fix2 (hPp : ⁅P, P⁆ = P) (hn : 7 ≤ n) (hP2 : CharTwo P)
    (hK : IsShort2 K) (hαw : IsAltBlockTypeWith K n α)
    (hsurj : ∀ g ∈ AltN.fix2 a b, ∃ (p : G) (hp : p ∈ K), p ∈ P ∧ α ⟨p, hp⟩ = g)
    (hQN : pCoreOf 2 K ≤ Subgroup.normalizer (P : Set G)) :
    IsAltBlockType P (n - 2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUK := hK.2.2.1.1
  have hexp := hK.2.2.1.2
  have hUQ : blockU K ≤ pCoreOf 2 K := hUK.trans inf_le_left
  have hUab : ∀ u ∈ blockU K, ∀ v ∈ blockU K, u * v = v * u := fun u hu v hv =>
    Subgroup.mem_centralizer_iff.mp (hUK hv).2 u (hUQ hu)
  have hbt := isAltBlockTypeWith_alphaRes hPK α hab hfix hPp hn hαw hsurj hUQ hUab hQN
  have hPO := pCoreOf_eq_inf hPK α hab hfix hn hαw.2.1 hsurj
  have hQPK : pCoreOf 2 P ≤ pCoreOf 2 K := by
    rw [hPO]
    exact inf_le_right
  have hUU : blockU P ≤ blockU K := Subgroup.commutator_mono hQPK hPK
  refine ⟨⟨?_, hP2, ⟨le_inf ?_ fun u hu => Subgroup.mem_centralizer_iff.mpr fun q hq => ?_,
    fun x hx => hexp x (hUU hx)⟩, Or.inl ?_, irreducible_of_altBlockTypeWith (by omega) hbt⟩,
    _, hbt⟩
  · intro N _ hN
    have hperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hPp
    by_contra hne
    have : Nontrivial (↥P ⧸ N) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply hne
      rw [eq_top_iff]
      intro x _
      have : (x : ↥P ⧸ N) = 1 := Subsingleton.elim _ _
      rwa [QuotientGroup.eq_one_iff] at this
    have hperfQ : Group.IsPerfect (↥P ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    have : Group.IsNilpotent (↥P ⧸ N) := hN.isNilpotent
    exact Group.IsPerfect.not_isSolvable (↥P ⧸ N) inferInstance
  · show ⁅pCoreOf 2 P, P⁆ ≤ pCoreOf 2 P
    rw [Subgroup.commutator_le]
    intro q hq p hp
    have e : ⁅q, p⁆ = q * (p * q⁻¹ * p⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 P).mul_mem hq ((Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 P hp) _).mp ((pCoreOf 2 P).inv_mem hq))
  · exact Subgroup.mem_centralizer_iff.mp (hUK (hUU hu)).2 q (hQPK hq)
  · exact isQuasisimple_of_mulEquiv_alt (by omega)
      ((QuotientGroup.quotientMulEquivOfEq hbt.2.1.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective _ hbt.1))

end Restrict

theorem c46Block_holds : C46Block G := by
  intro H R M L V K n α₀ hP h1 h2 hc hshort hαw₀ hn7 hn8 hIT hMKR
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨n', α, hn5', hn8', -, hαw, t, htR, htV, hRt, ht2, σ, hσ, hconj⟩, hMK⟩ := hc
  have hnn : n' = n := by
    have e1 : Nat.card (alternatingGroup (Fin n)) = Nat.card (alternatingGroup (Fin n')) :=
      Nat.card_congr (((QuotientGroup.quotientMulEquivOfEq hαw₀.2.1.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α₀ hαw₀.1)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hαw.2.1.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective α hαw.1))).toEquiv
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at e1
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have : Nontrivial (Fin n') := Fin.nontrivial_iff_two_le.mpr (by omega)
    have c1 := two_mul_card_alternatingGroup (α := Fin n)
    have c2 := two_mul_card_alternatingGroup (α := Fin n')
    rw [Fintype.card_perm, Fintype.card_fin] at c1 c2
    have hf : n.factorial = n'.factorial := by rw [← c1, ← c2, e1]
    exact ((Nat.factorial_inj (by omega)).mp hf).symm
  subst hnn
  obtain ⟨a, b, hab, rfl⟩ := hσ
  set W := omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) with hW
  set M0 := conjClosure L M with hM0
  have h := hP.hyp
  have hKH : K ≤ H := le_of_mem_cComp hP.comp
  have hM0K : M0 ≤ K := hP.le
  have hM0M : M0 ≤ M := C2Nine.conjClosure_le_M h
  have hM0perf : ⁅M0, M0⁆ = M0 := C2Nine.perfect_conjClosure_of_hyp h
  have hMM0 : M ≤ Subgroup.normalizer (M0 : Set G) := le_normalizer_conjClosure L M
  have hNK : M0 ≤ Subgroup.normalizer (K : Set G) := hM0K.trans Subgroup.le_normalizer
  have hO2KR : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 K)
        (hP.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 K)))
      (pCoreOf_isPGroup 2 K)
  have hO2M : pCoreOf 2 K ≤ M := (hO2KR.trans (pCoreOf_sup_le_of_hyp h hKH hNK)).trans h.le_M
  have hQN : pCoreOf 2 K ≤ Subgroup.normalizer (M0 : Set G) := hO2M.trans hMM0
  have hne : (M0.subgroupOf K).map α ≠ ⊥ := by
    intro hb
    apply hP.not_commutator_le
    have hM0O : M0 ≤ pCoreOf 2 K := by
      intro m hm
      have h0 : α ⟨m, hM0K hm⟩ = 1 := by
        have : α ⟨m, hM0K hm⟩ ∈ (M0.subgroupOf K).map α := ⟨⟨m, hM0K hm⟩, hm, rfl⟩
        rw [hb] at this
        exact this
      have hk : (⟨m, hM0K hm⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := hαw.2.1 ▸ MonoidHom.mem_ker.mpr h0
      rw [C2A3Orbits.pCoreOf_eq_map_pCore K]
      exact ⟨_, hk, rfl⟩
    rw [Subgroup.commutator_le]
    intro m hm k hk
    have h3 : k * m⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) _).mp
        ((pCoreOf 2 K).inv_mem (hM0O hm))
    have e : ⁅m, k⁆ = m * (k * m⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact (pCoreOf 2 K).mul_mem (hM0O hm) h3
  have hX := map_eq_fix2 hM0K hM0perf hn7 α hab hne
    (fun p hp hpP => comm_swap_of_mem hP.le_normalizer h1 (by omega) α hαw.1 hαw.2.1 htR htV
      hconj hMK (hM0M hpP) hp)
    (fun g hg => by
      obtain ⟨k, hkM, hk⟩ := exists_mem_of_comm_swap hP.le_normalizer h1 (by omega) α hαw.1
        hαw.2.1 hO2M htR htV hRt hconj hMK g (AltN.comm_swap_of_mem_fix2 hg)
      exact ⟨k, hk, hMM0 hkM⟩)
  have hfix : ∀ (p : G) (hp : p ∈ K), p ∈ M0 → α ⟨p, hp⟩ ∈ AltN.fix2 a b := fun p hp hpP =>
    hX ▸ ⟨⟨p, hp⟩, hpP, rfl⟩
  have hsurj : ∀ g ∈ AltN.fix2 a b, ∃ (p : G) (hp : p ∈ K), p ∈ M0 ∧ α ⟨p, hp⟩ = g := by
    intro g hg
    rw [← hX] at hg
    obtain ⟨⟨p, hp⟩, hpP, rfl⟩ := hg
    exact ⟨p, hp, hpP, rfl⟩
  have hP2 : CharTwo M0 := CharTwo.of_normal h.charTwo hM0M (C2Nine.normal_conjClosure L M)
  have hbt := isAltBlockType_of_fix2 hM0K α hab hfix hM0perf hn7 hP2 hshort hαw hsurj hQN
  refine ⟨hbt, ?_⟩
  obtain ⟨hsh, α', hbtw⟩ := hbt
  have hirr := irreducible_of_altBlockTypeWith (by omega) hbtw
  have hM0V : M0 ≤ Subgroup.normalizer (V : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right V M0
    rwa [h.V_comm] at this
  have hV2 : IsPGroup 2 ↥V := fun v => ⟨1, Subtype.ext (by simpa using h.V_elem.2 v v.2)⟩
  have hVQ : V ≤ pCoreOf 2 M0 := le_pCoreOf_of_le_normalizer 2 h.V_le hM0V hV2
  have hVU : V ≤ blockU M0 := by
    calc V = ⁅V, M0⁆ := h.V_comm.symm
      _ ≤ ⁅pCoreOf 2 M0, M0⁆ := Subgroup.commutator_mono hVQ le_rfl
  have hZn : M0 ≤ Subgroup.normalizer (blockZ M0 : Set G) := fun m hm =>
    Subgroup.mem_normalizer_fintype fun z hz => by
      rw [Subgroup.mem_centralizer_iff.mp hz.2 m hm, mul_inv_cancel_right]
      exact hz
  have hWn : M0 ≤ Subgroup.normalizer ((V ⊔ blockZ M0 : Subgroup G) : Set G) := fun m hm => by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hM0V hm),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZn hm)]
  rcases hirr.2 (V ⊔ blockZ M0) le_sup_right (sup_le hVU inf_le_left) hWn with hW' | hW'
  · exfalso
    apply h.V_ne
    have hVZ : V ≤ blockZ M0 := hW' ▸ le_sup_left
    rw [eq_bot_iff, ← h.V_comm, Subgroup.commutator_le]
    intro v hv m hm
    have hcm : m * v = v * m := Subgroup.mem_centralizer_iff.mp (hVZ hv).2 m hm
    rw [Subgroup.mem_bot, commutatorElement_def, ← hcm]
    group
  · have hUab : ∀ u ∈ blockU M0, ∀ v ∈ blockU M0, u * v = v * u := fun u hu v hv =>
      Subgroup.mem_centralizer_iff.mp (hsh.2.2.1.1 hv).2 u (hsh.2.2.1.1 hu).1
    exact le_antisymm hVU (commutator_le_of_le_sup hM0perf hM0V inf_le_right h.V_le
      hW'.symm.le hUab)

end CFSG.Quasithin.C41Pf
