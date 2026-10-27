module

public import CFSG.Quasithin.Vol2.GoldschmidtF431NFMain

public section

namespace CFSG.Quasithin.H13.F431.NF

open CFSG.QuasithinUnique
open scoped commutatorElement

section Img

variable {Mb : Type*} [Group Mb] {G : Type*} [Group G] {M₁ : Subgroup Mb} (b : ↥M₁ →* G)

@[expose] def kImg (X : Subgroup Mb) : Subgroup G := (X.subgroupOf M₁).map b

variable {b}

theorem mem_kImg {X : Subgroup Mb} {g : G} :
    g ∈ kImg b X ↔ ∃ (x : Mb) (hx : x ∈ M₁), x ∈ X ∧ b ⟨x, hx⟩ = g := by
  unfold kImg
  constructor
  · rintro ⟨⟨x, hx⟩, hxX, rfl⟩
    exact ⟨x, hx, hxX, rfl⟩
  · rintro ⟨x, hx, hxX, rfl⟩
    exact ⟨⟨x, hx⟩, hxX, rfl⟩

theorem mem_kImg_of_mem {X : Subgroup Mb} {x : Mb} (hx : x ∈ M₁) (hxX : x ∈ X) :
    b ⟨x, hx⟩ ∈ kImg b X :=
  mem_kImg.mpr ⟨x, hx, hxX, rfl⟩

theorem mem_kImg_iff (hb : Function.Injective b) {X : Subgroup Mb} {x : Mb} (hx : x ∈ M₁) :
    b ⟨x, hx⟩ ∈ kImg b X ↔ x ∈ X := by
  constructor
  · intro h
    obtain ⟨y, hy, hyX, hyx⟩ := mem_kImg.mp h
    have : (⟨y, hy⟩ : ↥M₁) = ⟨x, hx⟩ := hb hyx
    have hyx' : y = x := congrArg Subtype.val this
    rwa [← hyx']
  · exact mem_kImg_of_mem hx

theorem kImg_mono {X Y : Subgroup Mb} (h : X ≤ Y) : kImg b X ≤ kImg b Y := by
  rintro _ hg
  obtain ⟨x, hx, hxX, rfl⟩ := mem_kImg.mp hg
  exact mem_kImg_of_mem hx (h hxX)

theorem kImg_le_range (X : Subgroup Mb) : kImg b X ≤ b.range := by
  rintro _ hg
  obtain ⟨x, hx, -, rfl⟩ := mem_kImg.mp hg
  exact ⟨_, rfl⟩

theorem card_kImg (hb : Function.Injective b) {X : Subgroup Mb} (hX : X ≤ M₁) :
    Nat.card (kImg b X) = Nat.card X := by
  unfold kImg
  rw [Subgroup.card_map_of_injective hb]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem kImg_cj (n : Mb) (hn : n ∈ M₁) (W : Subgroup Mb) :
    kImg b (cj n W) = cj (b ⟨n, hn⟩) (kImg b W) := by
  ext g
  rw [mem_cj, mem_kImg, mem_kImg]
  constructor
  · rintro ⟨x, hx, hxW, rfl⟩
    refine ⟨n⁻¹ * x * n, M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hn) hx) hn, mem_cj.mp hxW, ?_⟩
    have : (⟨n⁻¹ * x * n, M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hn) hx) hn⟩ : ↥M₁) =
        ⟨n, hn⟩⁻¹ * ⟨x, hx⟩ * ⟨n, hn⟩ := rfl
    rw [this, map_mul, map_mul, map_inv]
  · rintro ⟨w, hw, hwW, hwg⟩
    refine ⟨n * w * n⁻¹, M₁.mul_mem (M₁.mul_mem hn hw) (M₁.inv_mem hn), ?_, ?_⟩
    · rw [mem_cj]
      have : n⁻¹ * (n * w * n⁻¹) * n = w := by group
      rwa [this]
    · have : (⟨n * w * n⁻¹, M₁.mul_mem (M₁.mul_mem hn hw) (M₁.inv_mem hn)⟩ : ↥M₁) =
          ⟨n, hn⟩ * ⟨w, hw⟩ * ⟨n, hn⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hwg]
      group

theorem comm_mem_M₁ {x y : Mb} (hx : x ∈ M₁) (hy : y ∈ M₁) : ⁅x, y⁆ ∈ M₁ := by
  rw [commutatorElement_def]
  exact M₁.mul_mem (M₁.mul_mem (M₁.mul_mem hx hy) (M₁.inv_mem hx)) (M₁.inv_mem hy)

theorem map_mul_mk {x y : Mb} (hx : x ∈ M₁) (hy : y ∈ M₁) :
    b ⟨x, hx⟩ * b ⟨y, hy⟩ = b ⟨x * y, M₁.mul_mem hx hy⟩ :=
  (map_mul b ⟨x, hx⟩ ⟨y, hy⟩).symm

theorem map_conj_mk {s x : Mb} (hs : s ∈ M₁) (hx : x ∈ M₁) :
    b ⟨s, hs⟩ * b ⟨x, hx⟩ * (b ⟨s, hs⟩)⁻¹ =
      b ⟨s * x * s⁻¹, M₁.mul_mem (M₁.mul_mem hs hx) (M₁.inv_mem hs)⟩ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem map_comm_mk {x y : Mb} (hx : x ∈ M₁) (hy : y ∈ M₁) :
    ⁅b ⟨x, hx⟩, b ⟨y, hy⟩⁆ = b ⟨⁅x, y⁆, comm_mem_M₁ hx hy⟩ := by
  rw [← map_commutatorElement]
  rfl

theorem map_eq_one_iff_mk (hb : Function.Injective b) {x : Mb} (hx : x ∈ M₁) :
    b ⟨x, hx⟩ = 1 ↔ x = 1 := by
  constructor
  · intro h
    have : (⟨x, hx⟩ : ↥M₁) = 1 := hb (h.trans (map_one b).symm)
    exact congrArg Subtype.val this
  · intro h
    subst h
    exact map_one b

end Img

section NFK

variable {Mb : Type*} [Group Mb]

structure NFK (T Q Z X Y M₁ M₂ : Subgroup Mb) (z v nr na : Mb) (q n : ℕ) : Prop where
  T_le₁ : T ≤ M₁
  T_le₂ : T ≤ M₂
  Z_le_Q : Z ≤ Q
  Q_le_T : Q ≤ T
  Q_norm : ∀ s ∈ T, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q
  Z_central : ∀ x ∈ Z, ∀ s ∈ T, s * x = x * s
  Z_exp : ∀ x ∈ Z, x * x = 1
  card_Z : Nat.card Z = q
  z_mem : z ∈ Z
  z_ne : z ≠ 1
  Q_comm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Z
  Q_sq : ∀ x ∈ Q, x * x ∈ Z
  card_Q : Nat.card Q = q ^ (2 * n + 1)
  card_T : Nat.card T = q ^ (3 * n)
  T_comm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ Q
  elem_abelian : ∀ E : Subgroup Mb, E ≤ Q → (∀ x ∈ E, x * x = 1) →
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ q ^ (n + 1)
  M₁_Z : ∀ y ∈ M₁, ∀ x ∈ Z, y * x * y⁻¹ ∈ Z
  M₁_Q : ∀ y ∈ M₁, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q
  M₁_trans : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ 1 → y ≠ 1 → ∃ m ∈ M₁, m * x * m⁻¹ = y
  X_le : X ≤ Q
  Y_le : Y ≤ Q
  Z_le_comm : Z ≤ ⁅X, Y⁆
  v_mem : v ∈ Q
  v_not_mem : v ∉ Z
  v_comm_X : ∀ a ∈ X, a * v = v * a
  v_comm_Y : ∀ b ∈ Y, b * v = v * b
  v_not_cent : ∀ y ∈ M₁, ∃ s ∈ T, ⁅s, y * v * y⁻¹⁆ ∉ Z
  nr_mem : nr ∈ M₁
  na_mem : na ∈ M₂
  X_eq : X = cj nr Y
  Y_eq : Y = cj na Z

variable {T Q Z X Y M₁ M₂ : Subgroup Mb} {z v nr na : Mb} {q n : ℕ}

theorem NFK.Z_le_M₁ (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) : Z ≤ M₁ :=
  D.Z_le_Q.trans (D.Q_le_T.trans D.T_le₁)

theorem NFK.Z_le_M₂ (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) : Z ≤ M₂ :=
  D.Z_le_Q.trans (D.Q_le_T.trans D.T_le₂)

theorem NFK.Q_le_M₁ (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) : Q ≤ M₁ :=
  D.Q_le_T.trans D.T_le₁

theorem NFK.Y_le_M₁ (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) : Y ≤ M₁ :=
  D.Y_le.trans D.Q_le_M₁

theorem NFK.Y_le_M₂ (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) : Y ≤ M₂ :=
  D.Y_le.trans (D.Q_le_T.trans D.T_le₂)

theorem NFK.X_le_M₁ (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) : X ≤ M₁ :=
  D.X_le.trans D.Q_le_M₁

theorem NFK.z_mem₁ (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) : z ∈ M₁ := D.Z_le_M₁ D.z_mem

theorem NFK.v_mem₁ (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) : v ∈ M₁ := D.Q_le_M₁ D.v_mem

theorem NFK.kImg_Y_eq (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) {G : Type*} [Group G]
    {b₁ : ↥M₁ →* G} {b₂ : ↥M₂ →* G}
    (agree : ∀ g (h1 : g ∈ M₁) (h2 : g ∈ M₂), b₁ ⟨g, h1⟩ = b₂ ⟨g, h2⟩) :
    kImg b₁ Y = cj (b₂ ⟨na, D.na_mem⟩) (kImg b₁ Z) := by
  ext g
  rw [mem_cj, mem_kImg, mem_kImg]
  constructor
  · rintro ⟨y, hy1, hyY, rfl⟩
    have hy2 : y ∈ M₂ := D.Y_le_M₂ hyY
    have hyZ : na⁻¹ * y * na ∈ Z := mem_cj.mp (D.Y_eq ▸ hyY)
    have hw1 : na⁻¹ * y * na ∈ M₁ := D.Z_le_M₁ hyZ
    have hw2 : na⁻¹ * y * na ∈ M₂ := D.Z_le_M₂ hyZ
    refine ⟨na⁻¹ * y * na, hw1, hyZ, ?_⟩
    rw [agree _ hw1 hw2, agree y hy1 hy2]
    have : (⟨na⁻¹ * y * na, hw2⟩ : ↥M₂) = ⟨na, D.na_mem⟩⁻¹ * ⟨y, hy2⟩ * ⟨na, D.na_mem⟩ := rfl
    rw [this, map_mul, map_mul, map_inv]
  · rintro ⟨w, hw1, hwZ, hwg⟩
    have hy : na * w * na⁻¹ ∈ Y := by
      rw [D.Y_eq, mem_cj]
      have : na⁻¹ * (na * w * na⁻¹) * na = w := by group
      rwa [this]
    have hy1 : na * w * na⁻¹ ∈ M₁ := D.Y_le_M₁ hy
    have hy2 : na * w * na⁻¹ ∈ M₂ := D.Y_le_M₂ hy
    have hw2 : w ∈ M₂ := D.Z_le_M₂ hwZ
    refine ⟨na * w * na⁻¹, hy1, hy, ?_⟩
    rw [agree _ hy1 hy2]
    have : (⟨na * w * na⁻¹, hy2⟩ : ↥M₂) = ⟨na, D.na_mem⟩ * ⟨w, hw2⟩ * ⟨na, D.na_mem⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, ← agree w hw1 hw2, hwg]
    group

theorem NFK.kImg_X_eq (D : NFK T Q Z X Y M₁ M₂ z v nr na q n) {G : Type*} [Group G]
    {b₁ : ↥M₁ →* G} {b₂ : ↥M₂ →* G}
    (agree : ∀ g (h1 : g ∈ M₁) (h2 : g ∈ M₂), b₁ ⟨g, h1⟩ = b₂ ⟨g, h2⟩) :
    kImg b₁ X = cj (b₁ ⟨nr, D.nr_mem⟩ * b₂ ⟨na, D.na_mem⟩) (kImg b₁ Z) := by
  rw [cj_mul, ← D.kImg_Y_eq agree, ← kImg_cj nr D.nr_mem Y, ← D.X_eq]

theorem NFK.not_isConj_img {G : Type*} [Group G] [Finite G] {b₁ : ↥M₁ →* G} {b₂ : ↥M₂ →* G}
    (hb₁ : Function.Injective b₁)
    (agree : ∀ g (h1 : g ∈ M₁) (h2 : g ∈ M₂), b₁ ⟨g, h1⟩ = b₂ ⟨g, h2⟩)
    (D : NFK T Q Z X Y M₁ M₂ z v nr na q n)
    (hsyl : IsSylowTwoOf (kImg b₁ T) ⊤)
    (hcent : ∀ x ∈ kImg b₁ Z, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ b₁.range) :
    ¬ IsConj (b₁ ⟨z, D.z_mem₁⟩) (b₁ ⟨v, D.v_mem₁⟩) := by
  refine not_isConj_of_nfDatum (S := kImg b₁ T) (Q := kImg b₁ Q) (Z := kImg b₁ Z)
    (M₁ := b₁.range) (A := kImg b₁ X) (B := kImg b₁ Y) (q := q) (n := n)
    { sylow := hsyl
      cent_le := hcent
      Z_le_Q := kImg_mono D.Z_le_Q
      Q_le_S := kImg_mono D.Q_le_T
      Q_norm := ?_
      Z_central := ?_
      Z_exp := ?_
      card_Z := by rw [card_kImg hb₁ D.Z_le_M₁]; exact D.card_Z
      z_mem := mem_kImg_of_mem _ D.z_mem
      z_ne := fun h => D.z_ne ((map_eq_one_iff_mk hb₁ _).mp h)
      Q_comm := ?_
      Q_sq := ?_
      card_Q := by rw [card_kImg hb₁ D.Q_le_M₁]; exact D.card_Q
      card_S := by rw [card_kImg hb₁ D.T_le₁]; exact D.card_T
      S_comm := ?_
      elem_abelian := ?_
      M₁_Z := ?_
      M₁_Q := ?_
      M₁_trans := ?_
      A_conj := ⟨_, D.kImg_X_eq agree⟩
      B_conj := ⟨_, D.kImg_Y_eq agree⟩
      A_le := kImg_mono D.X_le
      B_le := kImg_mono D.Y_le
      Z_le_comm := ?_
      v_mem := mem_kImg_of_mem _ D.v_mem
      v_not_mem := fun h => D.v_not_mem ((mem_kImg_iff hb₁ D.v_mem₁).mp h)
      v_comm_A := ?_
      v_comm_B := ?_
      v_not_cent := ?_ }
  · intro s hs x hx
    obtain ⟨t, ht1, htT, rfl⟩ := mem_kImg.mp hs
    obtain ⟨x', hx1, hxQ, rfl⟩ := mem_kImg.mp hx
    rw [map_conj_mk]
    exact mem_kImg_of_mem _ (D.Q_norm t htT x' hxQ)
  · intro x hx s hs
    obtain ⟨x', hx1, hxZ, rfl⟩ := mem_kImg.mp hx
    obtain ⟨t, ht1, htT, rfl⟩ := mem_kImg.mp hs
    rw [map_mul_mk, map_mul_mk]
    exact congrArg b₁ (Subtype.ext (D.Z_central x' hxZ t htT))
  · intro x hx
    obtain ⟨x', hx1, hxZ, rfl⟩ := mem_kImg.mp hx
    rw [map_mul_mk]
    exact (map_eq_one_iff_mk hb₁ _).mpr (D.Z_exp x' hxZ)
  · intro x hx y hy
    obtain ⟨x', hx1, hxQ, rfl⟩ := mem_kImg.mp hx
    obtain ⟨y', hy1, hyQ, rfl⟩ := mem_kImg.mp hy
    rw [map_comm_mk]
    exact mem_kImg_of_mem _ (D.Q_comm x' hxQ y' hyQ)
  · intro x hx
    obtain ⟨x', hx1, hxQ, rfl⟩ := mem_kImg.mp hx
    rw [map_mul_mk]
    exact mem_kImg_of_mem _ (D.Q_sq x' hxQ)
  · intro x hx y hy
    obtain ⟨x', hx1, hxT, rfl⟩ := mem_kImg.mp hx
    obtain ⟨y', hy1, hyT, rfl⟩ := mem_kImg.mp hy
    rw [map_comm_mk]
    exact mem_kImg_of_mem _ (D.T_comm x' hxT y' hyT)
  · intro E hEQ hsq hco
    set E' : Subgroup Mb := (E.comap b₁).map M₁.subtype with hE'
    have hE'Q : E' ≤ Q := by
      rintro _ ⟨y, hyE, rfl⟩
      obtain ⟨q', hq1, hqQ, hq⟩ := mem_kImg.mp (hEQ hyE)
      have : (⟨q', hq1⟩ : ↥M₁) = y := hb₁ hq
      rw [← this]
      exact hqQ
    have hsq' : ∀ x ∈ E', x * x = 1 := by
      rintro _ ⟨y, hyE, rfl⟩
      have h := hsq _ hyE
      have : y * y = 1 := hb₁ (by rw [map_mul, map_one]; exact h)
      exact congrArg Subtype.val this
    have hco' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
      rintro _ ⟨x, hxE, rfl⟩ _ ⟨y, hyE, rfl⟩
      have h := hco _ hxE _ hyE
      have : x * y = y * x := hb₁ (by rw [map_mul, map_mul]; exact h)
      exact congrArg Subtype.val this
    have h1 : (E.comap b₁).map b₁ = E := Subgroup.map_comap_eq_self (hEQ.trans (kImg_le_range Q))
    have hcard : Nat.card E = Nat.card E' := by
      calc Nat.card E = Nat.card ((E.comap b₁).map b₁) := by rw [h1]
        _ = Nat.card (E.comap b₁) := Subgroup.card_map_of_injective hb₁
        _ = Nat.card E' := (Subgroup.card_map_of_injective M₁.subtype_injective).symm
    rw [hcard]
    exact D.elem_abelian E' hE'Q hsq' hco'
  · rintro _ ⟨⟨m, hm⟩, rfl⟩ x hx
    obtain ⟨x', hx1, hxZ, rfl⟩ := mem_kImg.mp hx
    rw [map_conj_mk]
    exact mem_kImg_of_mem _ (D.M₁_Z m hm x' hxZ)
  · rintro _ ⟨⟨m, hm⟩, rfl⟩ x hx
    obtain ⟨x', hx1, hxQ, rfl⟩ := mem_kImg.mp hx
    rw [map_conj_mk]
    exact mem_kImg_of_mem _ (D.M₁_Q m hm x' hxQ)
  · intro x hx y hy hx1 hy1
    obtain ⟨x', hx1', hxZ, rfl⟩ := mem_kImg.mp hx
    obtain ⟨y', hy1', hyZ, rfl⟩ := mem_kImg.mp hy
    obtain ⟨m, hm, hmxy⟩ := D.M₁_trans x' hxZ y' hyZ
      (fun h => hx1 ((map_eq_one_iff_mk hb₁ _).mpr h))
      (fun h => hy1 ((map_eq_one_iff_mk hb₁ _).mpr h))
    refine ⟨b₁ ⟨m, hm⟩, ⟨_, rfl⟩, ?_⟩
    rw [map_conj_mk]
    exact congrArg b₁ (Subtype.ext hmxy)
  · intro g hg
    obtain ⟨z', hz1, hzZ, rfl⟩ := mem_kImg.mp hg
    set L : Subgroup Mb :=
      ((⁅kImg b₁ X, kImg b₁ Y⁆).comap b₁).map M₁.subtype with hL
    have hXY : ⁅X, Y⁆ ≤ L := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      have hx1 : x ∈ M₁ := D.X_le_M₁ hx
      have hy1 : y ∈ M₁ := D.Y_le_M₁ hy
      refine ⟨⟨⁅x, y⁆, comm_mem_M₁ hx1 hy1⟩, ?_, rfl⟩
      show b₁ ⟨⁅x, y⁆, comm_mem_M₁ hx1 hy1⟩ ∈ ⁅kImg b₁ X, kImg b₁ Y⁆
      rw [← map_comm_mk (b := b₁) hx1 hy1]
      exact Subgroup.commutator_mem_commutator (mem_kImg_of_mem hx1 hx) (mem_kImg_of_mem hy1 hy)
    obtain ⟨w, hw, hwz⟩ := hXY (D.Z_le_comm hzZ)
    have : w = ⟨z', hz1⟩ := Subtype.ext hwz
    rw [this] at hw
    exact hw
  · intro a ha
    obtain ⟨a', ha1, haX, rfl⟩ := mem_kImg.mp ha
    rw [map_mul_mk, map_mul_mk]
    exact congrArg b₁ (Subtype.ext (D.v_comm_X a' haX))
  · intro a ha
    obtain ⟨a', ha1, haY, rfl⟩ := mem_kImg.mp ha
    rw [map_mul_mk, map_mul_mk]
    exact congrArg b₁ (Subtype.ext (D.v_comm_Y a' haY))
  · rintro _ ⟨⟨m, hm⟩, rfl⟩
    obtain ⟨s, hsT, hs⟩ := D.v_not_cent m hm
    have hs1 : s ∈ M₁ := D.T_le₁ hsT
    have hw1 : m * v * m⁻¹ ∈ M₁ := M₁.mul_mem (M₁.mul_mem hm D.v_mem₁) (M₁.inv_mem hm)
    refine ⟨b₁ ⟨s, hs1⟩, mem_kImg_of_mem hs1 hsT, ?_⟩
    rw [map_conj_mk, map_comm_mk]
    intro h
    exact hs ((mem_kImg_iff hb₁ (comm_mem_M₁ hs1 hw1)).mp h)

end NFK

end CFSG.Quasithin.H13.F431.NF
