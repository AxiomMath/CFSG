module

public import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79NF

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]

structure Quo (Γ Z : Subgroup H) (G : Type) [Group G] where
  φ : ↥Γ →* G
  surj : Function.Surjective φ
  ker : φ.ker = Z.subgroupOf Γ

namespace Quo

variable {Γ Z : Subgroup H} {G : Type} [Group G] (Q : Quo Γ Z G)

theorem eq_one_iff {x : H} (hx : x ∈ Γ) : Q.φ ⟨x, hx⟩ = 1 ↔ x ∈ Z := by
  rw [← MonoidHom.mem_ker, Q.ker, Subgroup.mem_subgroupOf]

theorem eq_iff {x y : H} (hx : x ∈ Γ) (hy : y ∈ Γ) :
    Q.φ ⟨x, hx⟩ = Q.φ ⟨y, hy⟩ ↔ x⁻¹ * y ∈ Z := by
  rw [← Q.eq_one_iff (Γ.mul_mem (Γ.inv_mem hx) hy)]
  have : (⟨x⁻¹ * y, Γ.mul_mem (Γ.inv_mem hx) hy⟩ : ↥Γ) = (⟨x, hx⟩ : ↥Γ)⁻¹ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, map_inv, inv_mul_eq_one, eq_comm]

def pre (K : Subgroup G) : Subgroup H := (K.comap Q.φ).map Γ.subtype

theorem mem_pre_iff (K : Subgroup G) {x : H} :
    x ∈ Q.pre K ↔ ∃ hx : x ∈ Γ, Q.φ ⟨x, hx⟩ ∈ K := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem pre_le (K : Subgroup G) : Q.pre K ≤ Γ := by
  intro x hx
  exact ((Q.mem_pre_iff K).mp hx).1

theorem Z_le_pre (K : Subgroup G) (hZ : Z ≤ Γ) : Z ≤ Q.pre K := by
  intro z hz
  refine (Q.mem_pre_iff K).mpr ⟨hZ hz, ?_⟩
  rw [(Q.eq_one_iff (hZ hz)).mpr hz]
  exact K.one_mem

theorem pre_subgroupOf (K : Subgroup G) : (Q.pre K).subgroupOf Γ = K.comap Q.φ := by
  ext g
  rw [Subgroup.mem_subgroupOf, Q.mem_pre_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact h
  · intro h
    exact ⟨g.2, h⟩

theorem mem_Nor_iff (K : Subgroup G) (gq : G) :
    gq ∈ Nor K ↔ ∃ g : ↥Γ, Q.φ g = gq ∧ (g : H) ∈ Nor (Q.pre K) := by
  constructor
  · intro h
    obtain ⟨g, rfl⟩ := Q.surj gq
    refine ⟨g, rfl, ?_⟩
    have h1 : g ∈ (Nor K).comap Q.φ := h
    rw [Nor, Subgroup.comap_normalizer_eq_of_surjective K Q.surj] at h1
    have h2 : g ∈ (Nor (Q.pre K)).subgroupOf Γ := by
      rw [Nor, Subgroup.subgroupOf_normalizer_eq (Q.pre_le K), Q.pre_subgroupOf]
      exact h1
    exact h2
  · rintro ⟨g, rfl, hg⟩
    have h2 : g ∈ (Nor (Q.pre K)).subgroupOf Γ := hg
    rw [Nor, Subgroup.subgroupOf_normalizer_eq (Q.pre_le K), Q.pre_subgroupOf] at h2
    have h1 : g ∈ (Nor K).comap Q.φ := by
      rw [Nor, Subgroup.comap_normalizer_eq_of_surjective K Q.surj]
      exact h2
    exact h1

theorem pre_zpowers (hZ : Z ≤ Γ) {x : H} (hx : x ∈ Γ) :
    Q.pre (Subgroup.zpowers (Q.φ ⟨x, hx⟩)) = Subgroup.zpowers x ⊔ Z := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgΓ, hk⟩ := (Q.mem_pre_iff _).mp hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hk
    have h1 : Q.φ ⟨x ^ k, Γ.zpow_mem hx k⟩ = Q.φ ⟨g, hgΓ⟩ := by
      rw [← hk, ← map_zpow]
      rfl
    have h2 := (Q.eq_iff (Γ.zpow_mem hx k) hgΓ).mp h1
    have h3 : g = x ^ k * (x ^ k)⁻¹ * g := by group
    rw [h3, mul_assoc]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k) h2
  · refine sup_le ?_ (Q.Z_le_pre _ hZ)
    rw [Subgroup.zpowers_le]
    refine (Q.mem_pre_iff _).mpr ⟨hx, Subgroup.mem_zpowers _⟩

end Quo

structure QData (Γ Z : Subgroup H) (b t c : H) (J' : Subgroup H) : Prop where
  Z_le : Z ≤ Γ
  Z_norm : ∀ g ∈ Γ, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z
  b_mem : b ∈ Γ
  t_mem : t ∈ Γ
  c_mem : c ∈ Γ
  J'_le : J' ≤ Γ
  c_mem_J : c ∈ J'
  b3 : b ^ 3 = 1
  b_nmem : b ∉ Z
  t2 : t * t = 1
  t_nmem : t ∉ Z
  tb : t * b * t⁻¹ = b⁻¹
  c3 : c ^ 3 = 1
  c_nmem : c ∉ Z
  J'_iso : Nonempty (↥J' ≃* Equiv.Perm (Fin 3))
  J'_inf_Z : J' ⊓ Z = ⊥
  J'_comm_b : ∀ j ∈ J', j * b = b * j
  J'_comm_t : ∀ j ∈ J', j * t = t * j
  N_J : ∀ g ∈ Γ ⊓ Nor (Subgroup.zpowers b ⊔ Z), ∀ j ∈ J', ∃ j' ∈ J', ∃ z ∈ Z,
    g * j * g⁻¹ = j' * z
  struct_b : ∃ W : Subgroup H, W ≤ Γ ⊓ Nor (Subgroup.zpowers b ⊔ Z) ∧
    Nat.Coprime 3 (Nat.card W) ∧
    (∀ g ∈ Γ ⊓ Nor (Subgroup.zpowers b ⊔ Z), ∀ w ∈ W, ∃ w' ∈ W, ∃ z ∈ Z,
      g * w * g⁻¹ = w' * z) ∧
    (∀ g ∈ Γ ⊓ Nor (Subgroup.zpowers b ⊔ Z), ∃ w ∈ W,
      ∃ y ∈ Subgroup.closure ({b, t} : Set H), ∃ j ∈ J', ∃ z ∈ Z, g = w * y * j * z)
  struct_c : ∃ Wc : Subgroup H, Wc ≤ Γ ⊓ Nor (Subgroup.zpowers c ⊔ Z) ∧
    Nat.Coprime 3 (Nat.card Wc) ∧
    (∀ g ∈ Γ ⊓ Nor (Subgroup.zpowers c ⊔ Z), ∀ w ∈ Wc, ∃ w' ∈ Wc, ∃ z ∈ Z,
      g * w * g⁻¹ = w' * z) ∧
    (∀ g ∈ Γ ⊓ Nor (Subgroup.zpowers c ⊔ Z), ∃ w ∈ Wc,
      ∃ n ∈ Γ ⊓ Nor (Subgroup.zpowers c ⊔ Z) ⊓ Nor (Subgroup.zpowers b ⊔ Z), ∃ z ∈ Z,
        g = w * n * z)
  no2 : ∀ R : Subgroup H, R ≤ Γ → Z ≤ R → (∀ r ∈ R, ∃ k : ℕ, r ^ (2 ^ k) ∈ Z) →
    b ∈ Nor R → c ∈ Nor R → R ≤ Z
  weak : ∀ h ∈ Γ, (∀ k : ℤ, h * b ^ k * h⁻¹ ∈ Nor (Subgroup.zpowers b ⊔ Z)) →
    h * b * h⁻¹ ∈ Subgroup.zpowers b ⊔ Z

namespace Quo

variable {Γ Z : Subgroup H} {G : Type} [Group G] [Finite G] (Q : Quo Γ Z G)
variable {b t c : H} {J' : Subgroup H} (D : QData Γ Z b t c J')

theorem orderOf_b : orderOf (Q.φ ⟨b, D.b_mem⟩) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · have : (⟨b, D.b_mem⟩ : ↥Γ) ^ 3 = 1 := Subtype.ext (by simpa using D.b3)
    rw [← map_pow, this, map_one]
  · intro h1
    exact D.b_nmem ((Q.eq_one_iff D.b_mem).mp h1)

theorem orderOf_t : orderOf (Q.φ ⟨t, D.t_mem⟩) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · have : (⟨t, D.t_mem⟩ : ↥Γ) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using D.t2)
    rw [← map_pow, this, map_one]
  · intro h1
    exact D.t_nmem ((Q.eq_one_iff D.t_mem).mp h1)

theorem orderOf_c : orderOf (Q.φ ⟨c, D.c_mem⟩) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · have : (⟨c, D.c_mem⟩ : ↥Γ) ^ 3 = 1 := Subtype.ext (by simpa using D.c3)
    rw [← map_pow, this, map_one]
  · intro h1
    exact D.c_nmem ((Q.eq_one_iff D.c_mem).mp h1)

theorem tb_eq : Q.φ ⟨t, D.t_mem⟩ * Q.φ ⟨b, D.b_mem⟩ * (Q.φ ⟨t, D.t_mem⟩)⁻¹ =
    (Q.φ ⟨b, D.b_mem⟩)⁻¹ := by
  have h : (⟨t, D.t_mem⟩ : ↥Γ) * ⟨b, D.b_mem⟩ * (⟨t, D.t_mem⟩ : ↥Γ)⁻¹ =
      (⟨b, D.b_mem⟩ : ↥Γ)⁻¹ := Subtype.ext (by simpa using D.tb)
  have := congrArg Q.φ h
  rw [map_mul, map_mul, map_inv, map_inv] at this
  exact this

def Jq : Subgroup G := (J'.subgroupOf Γ).map Q.φ

theorem mem_Jq_iff {x : G} : x ∈ Q.Jq (J' := J') ↔ ∃ j : ↥Γ, (j : H) ∈ J' ∧ Q.φ j = x := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl⟩

theorem φ_mem_Jq {j : H} (hj : j ∈ J') : Q.φ ⟨j, D.J'_le hj⟩ ∈ Q.Jq (J' := J') :=
  (Q.mem_Jq_iff).mpr ⟨⟨j, D.J'_le hj⟩, hj, rfl⟩

include D in
theorem Jq_iso : Nonempty (↥(Q.Jq (J' := J')) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := D.J'_iso
  set K : Subgroup ↥Γ := J'.subgroupOf Γ with hK
  have hinj : Function.Injective (Q.φ.domRestrict K) := by
    intro a b hab
    have hab' : Q.φ (a : ↥Γ) = Q.φ (b : ↥Γ) := hab
    have h1 : (a : ↥Γ)⁻¹ * (b : ↥Γ) ∈ Q.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab', inv_mul_cancel]
    rw [Q.ker, Subgroup.mem_subgroupOf] at h1
    have h2 : ((a : ↥Γ)⁻¹ * (b : ↥Γ) : ↥Γ) ∈ K := K.mul_mem (K.inv_mem a.2) b.2
    have h3 : (((a : ↥Γ)⁻¹ * (b : ↥Γ) : ↥Γ) : H) ∈ J' ⊓ Z := ⟨h2, h1⟩
    rw [D.J'_inf_Z, Subgroup.mem_bot] at h3
    apply Subtype.ext
    apply Subtype.ext
    have : ((a : ↥Γ) : H)⁻¹ * ((b : ↥Γ) : H) = 1 := by simpa using h3
    exact (inv_mul_eq_one.mp this)
  let e1 : ↥K ≃* ↥(Q.φ.domRestrict K).range := MonoidHom.ofInjective hinj
  let e2 : ↥(Q.φ.domRestrict K).range ≃* ↥(K.map Q.φ) :=
    MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ _)
  let e3 : ↥K ≃* ↥J' := Subgroup.subgroupOfEquivOfLe D.J'_le
  exact ⟨(e1.trans e2).symm.trans (e3.trans e)⟩

theorem Jq_cen_b : Q.Jq (J' := J') ≤ Cen (Q.φ ⟨b, D.b_mem⟩) := by
  rintro x hx
  obtain ⟨j, hj, rfl⟩ := (Q.mem_Jq_iff).mp hx
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (D.J'_comm_b _ hj)

theorem Jq_cen_t : Q.Jq (J' := J') ≤ Cen (Q.φ ⟨t, D.t_mem⟩) := by
  rintro x hx
  obtain ⟨j, hj, rfl⟩ := (Q.mem_Jq_iff).mp hx
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (D.J'_comm_t _ hj)

theorem φ_eq_of_mul_mem {x y : ↥Γ} {z : H} (hz : z ∈ Z) (h : (x : H) = (y : H) * z) :
    Q.φ x = Q.φ y := by
  have := (Q.eq_iff y.2 x.2).mpr (by rw [h]; simpa using hz)
  exact this.symm

theorem mem_Nor_b_iff (gq : G) :
    gq ∈ Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) ↔
      ∃ g : ↥Γ, Q.φ g = gq ∧ (g : H) ∈ Nor (Subgroup.zpowers b ⊔ Z) := by
  rw [Q.mem_Nor_iff, Q.pre_zpowers D.Z_le D.b_mem]

theorem φ_mem_closure {y : H} (hy : y ∈ Subgroup.closure ({b, t} : Set H)) :
    ∃ hΓ : y ∈ Γ, Q.φ ⟨y, hΓ⟩ ∈
      Subgroup.closure ({Q.φ ⟨b, D.b_mem⟩, Q.φ ⟨t, D.t_mem⟩} : Set G) := by
  refine Subgroup.closure_induction
    (p := fun y _ => ∃ hΓ : y ∈ Γ, Q.φ ⟨y, hΓ⟩ ∈
      Subgroup.closure ({Q.φ ⟨b, D.b_mem⟩, Q.φ ⟨t, D.t_mem⟩} : Set G)) ?_ ?_ ?_ ?_ hy
  · rintro x (rfl | rfl)
    · exact ⟨D.b_mem, Subgroup.subset_closure (by simp)⟩
    · exact ⟨D.t_mem, Subgroup.subset_closure (by simp)⟩
  · refine ⟨Γ.one_mem, ?_⟩
    have : (⟨1, Γ.one_mem⟩ : ↥Γ) = 1 := rfl
    rw [this, map_one]
    exact Subgroup.one_mem _
  · rintro x y _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨Γ.mul_mem hx hy, ?_⟩
    have : (⟨x * y, Γ.mul_mem hx hy⟩ : ↥Γ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul]
    exact Subgroup.mul_mem _ hx' hy'
  · rintro x _ ⟨hx, hx'⟩
    refine ⟨Γ.inv_mem hx, ?_⟩
    have : (⟨x⁻¹, Γ.inv_mem hx⟩ : ↥Γ) = (⟨x, hx⟩ : ↥Γ)⁻¹ := rfl
    rw [this, map_inv]
    exact Subgroup.inv_mem _ hx'

theorem Nor_b_le_Nor_Jq :
    Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) ≤ Nor (Q.Jq (J' := J')) := by
  intro gq hgq
  obtain ⟨g, rfl, hg⟩ := (Q.mem_Nor_b_iff D gq).mp hgq
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := (Q.mem_Jq_iff).mp hx
  obtain ⟨j', hj', z, hz, hjz⟩ := D.N_J (g : H) ⟨g.2, hg⟩ (j : H) hj
  have h1 : Q.φ g * Q.φ j * (Q.φ g)⁻¹ = Q.φ ⟨j', D.J'_le hj'⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    apply Q.φ_eq_of_mul_mem hz
    exact hjz
  rw [h1]
  exact Q.φ_mem_Jq D hj'

theorem bq_mem_Nor : Q.φ ⟨b, D.b_mem⟩ ∈ Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) :=
  Subgroup.le_normalizer (Subgroup.mem_zpowers _)

theorem tq_mem_Nor : Q.φ ⟨t, D.t_mem⟩ ∈ Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) := by
  refine mem_Nor_zpowers_of_conj ?_
  rw [Q.tb_eq D]
  exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

theorem closure_Jq_le_Nor :
    Subgroup.closure ({Q.φ ⟨b, D.b_mem⟩, Q.φ ⟨t, D.t_mem⟩} : Set G) ⊔ Q.Jq (J' := J') ≤
      Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) := by
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Q.bq_mem_Nor D
    · exact Q.tq_mem_Nor D
  · intro x hx
    exact fs79_cen_le_nor_zpowers _ (Q.Jq_cen_b D hx)

theorem mem_Nor_x_iff (hZ : Z ≤ Γ) {x : H} (hx : x ∈ Γ) (gq : G) :
    gq ∈ Nor (Subgroup.zpowers (Q.φ ⟨x, hx⟩)) ↔
      ∃ g : ↥Γ, Q.φ g = gq ∧ (g : H) ∈ Nor (Subgroup.zpowers x ⊔ Z) := by
  rw [Q.mem_Nor_iff, Q.pre_zpowers hZ hx]

theorem image_le_Opp (hZ : Z ≤ Γ) {x : H} (hx : x ∈ Γ) (W : Subgroup H)
    (hW : W ≤ Γ ⊓ Nor (Subgroup.zpowers x ⊔ Z)) (hcop : Nat.Coprime 3 (Nat.card W))
    (hnorm : ∀ g ∈ Γ ⊓ Nor (Subgroup.zpowers x ⊔ Z), ∀ w ∈ W, ∃ w' ∈ W, ∃ z ∈ Z,
      g * w * g⁻¹ = w' * z) :
    (W.subgroupOf Γ).map Q.φ ≤ Opp 3 (Nor (Subgroup.zpowers (Q.φ ⟨x, hx⟩))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWΓ : W ≤ Γ := hW.trans inf_le_left
  refine L14.le_Opp_of_normalized ?_ ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    refine (Q.mem_Nor_x_iff hZ hx _).mpr ⟨w, rfl, ?_⟩
    exact (hW hw).2
  · intro h hh y hy
    obtain ⟨g, rfl, hg⟩ := (Q.mem_Nor_x_iff hZ hx h).mp hh
    obtain ⟨w, hw, rfl⟩ := hy
    obtain ⟨w', hw', z, hz, hwz⟩ := hnorm (g : H) ⟨g.2, hg⟩ (w : H) hw
    refine ⟨⟨w', hWΓ hw'⟩, hw', ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (Q.φ_eq_of_mul_mem hz hwz).symm
  · have h1 : Nat.card ((W.subgroupOf Γ).map Q.φ) ∣ Nat.card (W.subgroupOf Γ) :=
      Subgroup.card_map_dvd (W.subgroupOf Γ) Q.φ
    have h2 : Nat.card (W.subgroupOf Γ) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWΓ).toEquiv
    rw [h2] at h1
    exact hcop.coprime_dvd_right h1

theorem setMul_b :
    setMul (Opp 3 (Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩))))
      (Subgroup.closure ({Q.φ ⟨b, D.b_mem⟩, Q.φ ⟨t, D.t_mem⟩} : Set G) ⊔ Q.Jq (J' := J')) =
      Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) := by
  ext x
  constructor
  · rintro ⟨o, ho, m, hm, rfl⟩
    exact (Nor _).mul_mem (L14.Opp_le 3 _ ho) (Q.closure_Jq_le_Nor D hm)
  · intro hx
    obtain ⟨g, rfl, hg⟩ := (Q.mem_Nor_x_iff D.Z_le D.b_mem x).mp hx
    obtain ⟨W, hWle, hWcop, hWn, hdec⟩ := D.struct_b
    obtain ⟨w, hw, y, hy, j, hj, z, hz, hgw⟩ := hdec (g : H) ⟨g.2, hg⟩
    have hwΓ : w ∈ Γ := (hWle hw).1
    obtain ⟨hyΓ, hyc⟩ := Q.φ_mem_closure D hy
    have hjΓ : j ∈ Γ := D.J'_le hj
    have hzΓ : z ∈ Γ := D.Z_le hz
    refine ⟨Q.φ ⟨w, hwΓ⟩, ?_, Q.φ ⟨y, hyΓ⟩ * Q.φ ⟨j, hjΓ⟩, ?_, ?_⟩
    · exact Q.image_le_Opp D.Z_le D.b_mem W hWle hWcop hWn ⟨⟨w, hwΓ⟩, hw, rfl⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyc)
        (Subgroup.mem_sup_right (Q.φ_mem_Jq D hj))
    · have : g = ⟨w, hwΓ⟩ * (⟨y, hyΓ⟩ * ⟨j, hjΓ⟩) * ⟨z, hzΓ⟩ :=
        Subtype.ext (by simp [hgw, mul_assoc])
      rw [this, map_mul, map_mul, map_mul, (Q.eq_one_iff hzΓ).mpr hz, mul_one]

theorem setMul_c :
    setMul (Opp 3 (Nor (Subgroup.zpowers (Q.φ ⟨c, D.c_mem⟩))))
      (Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) ⊓ Nor (Subgroup.zpowers (Q.φ ⟨c, D.c_mem⟩))) =
      Nor (Subgroup.zpowers (Q.φ ⟨c, D.c_mem⟩)) := by
  ext x
  constructor
  · rintro ⟨o, ho, m, hm, rfl⟩
    exact (Nor _).mul_mem (L14.Opp_le 3 _ ho) hm.2
  · intro hx
    obtain ⟨g, rfl, hg⟩ := (Q.mem_Nor_x_iff D.Z_le D.c_mem x).mp hx
    obtain ⟨Wc, hWle, hWcop, hWn, hdec⟩ := D.struct_c
    obtain ⟨w, hw, n, hn, z, hz, hgw⟩ := hdec (g : H) ⟨g.2, hg⟩
    have hwΓ : w ∈ Γ := (hWle hw).1
    have hnΓ : n ∈ Γ := hn.1.1
    have hzΓ : z ∈ Γ := D.Z_le hz
    refine ⟨Q.φ ⟨w, hwΓ⟩, ?_, Q.φ ⟨n, hnΓ⟩, ⟨?_, ?_⟩, ?_⟩
    · exact Q.image_le_Opp D.Z_le D.c_mem Wc hWle hWcop hWn ⟨⟨w, hwΓ⟩, hw, rfl⟩
    · exact (Q.mem_Nor_x_iff D.Z_le D.b_mem _).mpr ⟨⟨n, hnΓ⟩, rfl, hn.2⟩
    · exact (Q.mem_Nor_x_iff D.Z_le D.c_mem _).mpr ⟨⟨n, hnΓ⟩, rfl, hn.1.2⟩
    · have : g = ⟨w, hwΓ⟩ * ⟨n, hnΓ⟩ * ⟨z, hzΓ⟩ := Subtype.ext (by simpa using hgw)
      rw [this, map_mul, map_mul, (Q.eq_one_iff hzΓ).mpr hz, mul_one]

theorem no_two_quot (R : Subgroup G) (hR : IsPGroup 2 R)
    (hBR : Subgroup.closure ({Q.φ ⟨b, D.b_mem⟩, Q.φ ⟨c, D.c_mem⟩} : Set G) ≤ Nor R) :
    R = ⊥ := by
  have hbR : Q.φ ⟨b, D.b_mem⟩ ∈ Nor R := hBR (Subgroup.subset_closure (by simp))
  have hcR : Q.φ ⟨c, D.c_mem⟩ ∈ Nor R := hBR (Subgroup.subset_closure (by simp))
  have hle : Q.pre R ≤ Z := by
    refine D.no2 (Q.pre R) (Q.pre_le R) (Q.Z_le_pre R D.Z_le) ?_ ?_ ?_
    · intro r hr
      obtain ⟨hrΓ, hrR⟩ := (Q.mem_pre_iff R).mp hr
      obtain ⟨k, hk⟩ := hR ⟨_, hrR⟩
      refine ⟨k, ?_⟩
      have h1 : Q.φ ⟨r ^ (2 ^ k), Γ.pow_mem hrΓ _⟩ = 1 := by
        have := congrArg Subtype.val hk
        simpa [← map_pow] using this
      exact (Q.eq_one_iff (Γ.pow_mem hrΓ _)).mp h1
    · refine Subgroup.mem_normalizer_fintype fun r hr => ?_
      obtain ⟨hrΓ, hrR⟩ := (Q.mem_pre_iff R).mp hr
      refine (Q.mem_pre_iff R).mpr ⟨Γ.mul_mem (Γ.mul_mem D.b_mem hrΓ) (Γ.inv_mem D.b_mem), ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp hbR (Q.φ ⟨r, hrΓ⟩)).mp hrR
      have e : (⟨b * r * b⁻¹, Γ.mul_mem (Γ.mul_mem D.b_mem hrΓ) (Γ.inv_mem D.b_mem)⟩ : ↥Γ) =
          ⟨b, D.b_mem⟩ * ⟨r, hrΓ⟩ * ⟨b, D.b_mem⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact this
    · refine Subgroup.mem_normalizer_fintype fun r hr => ?_
      obtain ⟨hrΓ, hrR⟩ := (Q.mem_pre_iff R).mp hr
      refine (Q.mem_pre_iff R).mpr ⟨Γ.mul_mem (Γ.mul_mem D.c_mem hrΓ) (Γ.inv_mem D.c_mem), ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp hcR (Q.φ ⟨r, hrΓ⟩)).mp hrR
      have e : (⟨c * r * c⁻¹, Γ.mul_mem (Γ.mul_mem D.c_mem hrΓ) (Γ.inv_mem D.c_mem)⟩ : ↥Γ) =
          ⟨c, D.c_mem⟩ * ⟨r, hrΓ⟩ * ⟨c, D.c_mem⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact this
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := Q.surj x
  have hg : (g : H) ∈ Q.pre R := (Q.mem_pre_iff R).mpr ⟨g.2, hx⟩
  have := (Q.eq_one_iff g.2).mpr (hle hg)
  simpa using this

theorem φ_conj_zpow (g : ↥Γ) (k : ℤ) (hΓ : (g : H) * b ^ k * (g : H)⁻¹ ∈ Γ) :
    Q.φ ⟨(g : H) * b ^ k * (g : H)⁻¹, hΓ⟩ =
      Q.φ g * (Q.φ ⟨b, D.b_mem⟩) ^ k * (Q.φ g)⁻¹ := by
  have : (⟨(g : H) * b ^ k * (g : H)⁻¹, hΓ⟩ : ↥Γ) = g * (⟨b, D.b_mem⟩ : ↥Γ) ^ k * g⁻¹ :=
    Subtype.ext (by simp)
  rw [this, map_mul, map_mul, map_zpow, map_inv]

theorem weak_quot (h : G)
    (hh : conjBy h (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) ≤
      Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩))) :
    conjBy h (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) =
      Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩) := by
  obtain ⟨g, rfl⟩ := Q.surj h
  have hΓk : ∀ k : ℤ, (g : H) * b ^ k * (g : H)⁻¹ ∈ Γ := fun k =>
    Γ.mul_mem (Γ.mul_mem g.2 (Γ.zpow_mem D.b_mem k)) (Γ.inv_mem g.2)
  have hk : ∀ k : ℤ, (g : H) * b ^ k * (g : H)⁻¹ ∈ Nor (Subgroup.zpowers b ⊔ Z) := by
    intro k
    have hmem : Q.φ g * (Q.φ ⟨b, D.b_mem⟩) ^ k * (Q.φ g)⁻¹ ∈
        Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) := by
      apply hh
      refine ⟨(Q.φ ⟨b, D.b_mem⟩) ^ k, Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k, ?_⟩
      simp [MulAut.conj_apply]
    obtain ⟨g', hg', hg'N⟩ := (Q.mem_Nor_x_iff D.Z_le D.b_mem _).mp hmem
    have e : Q.φ ⟨(g : H) * b ^ k * (g : H)⁻¹, hΓk k⟩ = Q.φ g' := by
      rw [hg', Q.φ_conj_zpow D g k (hΓk k)]
    have hz := (Q.eq_iff (hΓk k) g'.2).mp e
    have hx : (g : H) * b ^ k * (g : H)⁻¹ =
        (g' : H) * (((g : H) * b ^ k * (g : H)⁻¹)⁻¹ * (g' : H))⁻¹ := by group
    rw [hx]
    refine (Nor _).mul_mem hg'N ((Nor _).inv_mem ?_)
    exact Subgroup.le_normalizer (Subgroup.mem_sup_right hz)
  have hwk := D.weak (g : H) g.2 hk
  rw [← Q.pre_zpowers D.Z_le D.b_mem] at hwk
  obtain ⟨hΓ, hmem⟩ := (Q.mem_pre_iff _).mp hwk
  have hconj1 : Q.φ g * Q.φ ⟨b, D.b_mem⟩ * (Q.φ g)⁻¹ ∈
      Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩) := by
    have e : (⟨(g : H) * b * (g : H)⁻¹, hΓ⟩ : ↥Γ) = g * ⟨b, D.b_mem⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at hmem
    exact hmem
  have hle : conjBy (Q.φ g) (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩)) ≤
      Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have e : (MulAut.conj (Q.φ g)).toMonoidHom ((Q.φ ⟨b, D.b_mem⟩) ^ k) =
        (Q.φ g * Q.φ ⟨b, D.b_mem⟩ * (Q.φ g)⁻¹) ^ k := by
      have := map_zpow (MulAut.conj (Q.φ g)) (Q.φ ⟨b, D.b_mem⟩) k
      simpa [MulAut.conj_apply] using this
    rw [e]
    exact Subgroup.zpow_mem _ hconj1 k
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [Subgroup.card_map_of_injective (MulAut.conj (Q.φ g)).injective])

end Quo

theorem odd_Opp_of_no_two {G : Type} [Group G] [Finite G] {A : Subgroup G} (hA : IsPGroup 3 A)
    (hno : ∀ R : Subgroup G, IsPGroup 2 R → A ≤ Nor R → R = ⊥) :
    Odd (Nat.card (Opp 3 (⊤ : Subgroup G))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := Opp 3 (⊤ : Subgroup G) with hO
  by_contra hodd
  have h2dvd : 2 ∣ Nat.card O := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have hOcop : Nat.Coprime 3 (Nat.card O) := L14.Opp_coprime 3 (⊤ : Subgroup G)
  have h3dvd : ¬ 3 ∣ Nat.card O := fun hd =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hOcop hd
  have hOn : O.Normal := ⟨fun x hx g => by
    simpa using L14.Opp_conj_mem (p := 3) (H := (⊤ : Subgroup G)) (Subgroup.mem_top g) hx⟩
  have hAO : A ≤ Subgroup.normalizer (O : Set G) := by
    haveI := hOn
    exact Subgroup.le_normalizer_of_normal
  obtain ⟨R, hRsyl, -, hAR⟩ := CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime
    (q := 3) (r := 2) (A := A) (K := O) (P := ⊥) Nat.prime_three Nat.prime_two hA hAO h3dvd
    bot_le IsPGroup.of_bot Subgroup.le_normalizer_of_normal
  have hR2 : IsPGroup 2 R := CFSG.ABGLocalTools.IsSylowOf.isPGroup hRsyl
  have hRbot : R = ⊥ := hno R hR2 hAR
  have hndvd : ¬ 2 ∣ R.relIndex O := (CFSG.ABGLocalTools.isSylowOf_iff.mp hRsyl).2.2
  exact hndvd (by rw [hRbot, Subgroup.relIndex_bot_left]; exact h2dvd)

theorem isPGroup_closure_pair {G : Type} [Group G] [Finite G] {x y : G} (hxy : x * y = y * x)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) : IsPGroup 3 (Subgroup.closure ({x, y} : Set G)) := by
  have hc : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  rw [hc]
  refine IsPGroup.to_sup_of_normal_left' (isPGroup_zpowers_of_pow_three hx)
    (isPGroup_zpowers_of_pow_three hy) ?_
  rw [Subgroup.zpowers_le]
  exact mem_Nor_zpowers_of_comm hxy.symm

end CFSG.RankThree.PartTwo.Sec21.FF81
