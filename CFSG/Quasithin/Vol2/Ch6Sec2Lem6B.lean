module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.F7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mul_self_eq_one_ch626 {E : Subgroup G} (hE : IsElemAbelian 2 E) {x : G} (hx : x ∈ E) :
    x * x = 1 := by
  have := hE.2 x hx
  rwa [pow_two] at this

theorem inv_eq_self_ch626 {E : Subgroup G} (hE : IsElemAbelian 2 E) {x : G} (hx : x ∈ E) :
    x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one_ch626 hE hx)

theorem mem_normalizer_of_conjSub_eq_ch626 {H : Subgroup G} {g : G} (h : conjSub g H = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ conjSub g H := by
      rw [mem_conjSub]
      simpa [mul_assoc] using hx
    rwa [h] at this
  · intro hx
    rw [← h, mem_conjSub] at hx
    simpa [mul_assoc] using hx

theorem mul_mem_of_relIndex_two_ch626 {H K : Subgroup G} (h2 : H.relIndex K = 2) {x y : G}
    (hx : x ∈ K) (hy : y ∈ K) (hxH : x ∉ H) (hyH : y ∉ H) : x * y ∈ H := by
  have hidx : (H.subgroupOf K).index = 2 := h2
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
    ⟨fun h => absurd h hxH, fun h => absurd h hyH⟩
  rw [Subgroup.mem_subgroupOf] at this
  exact this

theorem comm_commute_ch626 {X : Subgroup G} (hX : IsElemAbelian 2 X) {x a : G} (hx : x ∈ X)
    (ha : a ∈ Subgroup.normalizer (X : Set G)) (ha2 : a * a = 1) :
    (x * a * x⁻¹ * a⁻¹) * a = a * (x * a * x⁻¹ * a⁻¹) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hx' : a * x * a ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp ha x).mp hx
    rwa [hai] at this
  have hxi : x⁻¹ = x := inv_eq_self_ch626 hX hx
  have hcomm : x * (a * x * a) = (a * x * a) * x := B2F.isElemAbelian_comm hX hx hx'
  rw [hai, hxi]
  calc x * a * x * a * a = x * (a * x * a) * a := by group
    _ = (a * x * a) * x * a := by rw [hcomm]
    _ = a * (x * a * x * a) := by group

variable [Finite G]

theorem card_le_mul_card_centralizer_ch626 {K B : Subgroup G} {a : G}
    (hB : ∀ k ∈ K, k * a * k⁻¹ * a⁻¹ ∈ B) (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b = b * k)
    (hBB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    Nat.card K ≤ Nat.card B * Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  let f : ↥K →* ↥B :=
    { toFun := fun k => ⟨k * a * (k : G)⁻¹ * a⁻¹, hB k k.2⟩
      map_one' := by ext; simp
      map_mul' := fun k k' => by
        apply Subtype.ext
        show (k : G) * k' * a * ((k : G) * k')⁻¹ * a⁻¹ =
          ((k : G) * a * (k : G)⁻¹ * a⁻¹) * ((k' : G) * a * (k' : G)⁻¹ * a⁻¹)
        have h1 := hKB k k.2 _ (hB k' k'.2)
        have h2 := hBB _ (hB k k.2) _ (hB k' k'.2)
        calc (k : G) * k' * a * ((k : G) * k')⁻¹ * a⁻¹
            = (k : G) * ((k' : G) * a * (k' : G)⁻¹ * a⁻¹) * (a * (k : G)⁻¹ * a⁻¹) := by group
          _ = ((k' : G) * a * (k' : G)⁻¹ * a⁻¹) * k * (a * (k : G)⁻¹ * a⁻¹) := by rw [h1]
          _ = ((k' : G) * a * (k' : G)⁻¹ * a⁻¹) * ((k : G) * a * (k : G)⁻¹ * a⁻¹) := by group
          _ = _ := h2.symm }
  have hker : Nat.card f.ker ≤ Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) := by
    have hle : f.ker.map K.subtype ≤ K ⊓ Subgroup.centralizer ({a} : Set G) := by
      rintro _ ⟨k, hk, rfl⟩
      have hk1 : f k = 1 := hk
      have hk' : (k : G) * a * (k : G)⁻¹ * a⁻¹ = 1 := congrArg Subtype.val hk1
      refine ⟨k.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      show (k : G) * a = a * k
      calc (k : G) * a = (k : G) * a * (k : G)⁻¹ * a⁻¹ * (a * k) := by group
        _ = a * k := by rw [hk', one_mul]
    calc Nat.card f.ker = Nat.card (f.ker.map K.subtype) :=
          (Subgroup.card_map_of_injective K.subtype_injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  have hrange : Nat.card f.range ≤ Nat.card B := by
    calc Nat.card f.range ≤ Nat.card (⊤ : Subgroup ↥B) := Subgroup.card_le_of_le le_top
      _ = Nat.card B := Subgroup.card_top
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h1
  calc Nat.card K = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) * Nat.card B :=
        Nat.mul_le_mul hker hrange
    _ = _ := mul_comm _ _

structure Pair626 (X Y : Subgroup G) : Prop where
  elemX : IsElemAbelian 2 X
  elemY : IsElemAbelian 2 Y
  cardX : Nat.card X = 16
  cardY : Nat.card Y = 16
  idxA : (Y ⊓ Subgroup.normalizer (X : Set G)).relIndex Y = 2
  idxU : (X ⊓ Subgroup.normalizer (Y : Set G)).relIndex X = 2
  cardB : Nat.card ↥(X ⊓ Y) = 2
  centA : ∀ a ∈ Y ⊓ Subgroup.normalizer (X : Set G), a ∈ Subgroup.centralizer (X : Set G) →
    a ∈ X
  centU : ∀ u ∈ X ⊓ Subgroup.normalizer (Y : Set G), u ∈ Subgroup.centralizer (Y : Set G) →
    u ∈ Y
  fixX : ∀ a ∈ Y ⊓ Subgroup.normalizer (X : Set G), a ∉ Subgroup.centralizer (X : Set G) →
    Nat.card ↥(X ⊓ Subgroup.centralizer ({a} : Set G)) ≤ 4
  fixY : ∀ u ∈ X ⊓ Subgroup.normalizer (Y : Set G), u ∉ Subgroup.centralizer (Y : Set G) →
    Nat.card ↥(Y ⊓ Subgroup.centralizer ({u} : Set G)) ≤ 4
  uniqX : ∀ g : G, X ⊓ Subgroup.normalizer (Y : Set G) ≤ conjSub g X → conjSub g X = X
  uniqY : ∀ g : G, Y ⊓ Subgroup.normalizer (X : Set G) ≤ conjSub g Y → conjSub g Y = Y
  conjXY : ∃ c : G, Y = conjSub c X

namespace Pair626

variable {X Y : Subgroup G}

omit [Finite G] in
theorem symm (p : Pair626 X Y) : Pair626 Y X where
  elemX := p.elemY
  elemY := p.elemX
  cardX := p.cardY
  cardY := p.cardX
  idxA := p.idxU
  idxU := p.idxA
  cardB := by rw [inf_comm]; exact p.cardB
  centA := p.centU
  centU := p.centA
  fixX := p.fixY
  fixY := p.fixX
  uniqX := p.uniqY
  uniqY := p.uniqX
  conjXY := by
    obtain ⟨c, hc⟩ := p.conjXY
    exact ⟨c⁻¹, by rw [hc, conjSub_conjSub_inv]⟩

omit [Finite G] in
theorem card_A (p : Pair626 X Y) : Nat.card ↥(Y ⊓ Subgroup.normalizer (X : Set G)) = 8 := by
  have h1 := Subgroup.relIndex_mul_card (H := Y ⊓ Subgroup.normalizer (X : Set G)) (K := Y)
  rw [inf_of_le_left (inf_le_left : Y ⊓ Subgroup.normalizer (X : Set G) ≤ Y), p.idxA,
    p.cardY] at h1
  omega

omit [Finite G] in
theorem card_U (p : Pair626 X Y) : Nat.card ↥(X ⊓ Subgroup.normalizer (Y : Set G)) = 8 :=
  p.symm.card_A

omit [Finite G] in
theorem B_le_A : X ⊓ Y ≤ Y ⊓ Subgroup.normalizer (X : Set G) :=
  fun _ hb => ⟨hb.2, Subgroup.le_normalizer hb.1⟩

omit [Finite G] in
theorem B_le_U : X ⊓ Y ≤ X ⊓ Subgroup.normalizer (Y : Set G) :=
  fun _ hb => ⟨hb.1, Subgroup.le_normalizer hb.2⟩

omit [Finite G] in
theorem comm_mem_B {a u : G} (ha : a ∈ Y ⊓ Subgroup.normalizer (X : Set G))
    (hu : u ∈ X ⊓ Subgroup.normalizer (Y : Set G)) : a * u * a⁻¹ * u⁻¹ ∈ X ⊓ Y := by
  refine ⟨X.mul_mem ((Subgroup.mem_normalizer_iff.mp ha.2 u).mp hu.1) (X.inv_mem hu.1), ?_⟩
  have h1 : u * a⁻¹ * u⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hu.2 _).mp (Y.inv_mem ha.1)
  have e : a * u * a⁻¹ * u⁻¹ = a * (u * a⁻¹ * u⁻¹) := by group
  rw [e]
  exact Y.mul_mem ha.1 h1

omit [Finite G] in
theorem comm_mem_B' {a u : G} (ha : a ∈ Y ⊓ Subgroup.normalizer (X : Set G))
    (hu : u ∈ X ⊓ Subgroup.normalizer (Y : Set G)) : u * a * u⁻¹ * a⁻¹ ∈ X ⊓ Y := by
  have := (X ⊓ Y).inv_mem (comm_mem_B ha hu)
  have e : (a * u * a⁻¹ * u⁻¹)⁻¹ = u * a * u⁻¹ * a⁻¹ := by group
  rwa [e] at this

theorem mem_B_of_commute_U (p : Pair626 X Y) {a : G}
    (ha : a ∈ Y ⊓ Subgroup.normalizer (X : Set G))
    (hc : ∀ u ∈ X ⊓ Subgroup.normalizer (Y : Set G), a * u = u * a) : a ∈ X ⊓ Y := by
  by_cases haX : a ∈ Subgroup.centralizer (X : Set G)
  · exact ⟨p.centA a ha haX, ha.1⟩
  · exfalso
    have h1 := p.fixX a ha haX
    have hle : X ⊓ Subgroup.normalizer (Y : Set G) ≤
        X ⊓ Subgroup.centralizer ({a} : Set G) :=
      fun u hu => ⟨hu.1, Subgroup.mem_centralizer_singleton_iff.mpr (hc u hu).symm⟩
    have h2 := Subgroup.card_le_of_le hle
    rw [p.card_U] at h2
    omega

theorem mem_B_of_commute_A (p : Pair626 X Y) {x : G} (hx : x ∈ X)
    (hc : ∀ a ∈ Y ⊓ Subgroup.normalizer (X : Set G), x * a = a * x) : x ∈ X ⊓ Y := by
  have hAY : Y ⊓ Subgroup.normalizer (X : Set G) ≤ conjSub x Y := by
    intro a ha
    rw [mem_conjSub]
    have e : x⁻¹ * a * x = a := by rw [mul_assoc, ← hc a ha, inv_mul_cancel_left]
    rw [e]
    exact ha.1
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) :=
    mem_normalizer_of_conjSub_eq_ch626 (p.uniqY x hAY)
  have := p.symm.mem_B_of_commute_U (a := x) ⟨hx, hxN⟩ (fun a ha => hc a ha)
  rwa [inf_comm] at this

theorem centralizer_le_U (p : Pair626 X Y) {a : G}
    (ha : a ∈ Y ⊓ Subgroup.normalizer (X : Set G)) (haB : a ∉ X ⊓ Y) :
    X ⊓ Subgroup.centralizer ({a} : Set G) ≤ X ⊓ Subgroup.normalizer (Y : Set G) := by
  have haC : a ∉ Subgroup.centralizer (X : Set G) := fun h => haB ⟨p.centA a ha h, ha.1⟩
  have h4 := p.fixX a ha haC
  have hcard := card_le_mul_card_centralizer_ch626 (K := X ⊓ Subgroup.normalizer (Y : Set G))
    (B := X ⊓ Y) (a := a) (fun u hu => comm_mem_B' ha hu)
    (fun u hu b hb => B2F.isElemAbelian_comm p.elemX hu.1 hb.1)
    (fun b hb b' hb' => B2F.isElemAbelian_comm p.elemX hb.1 hb'.1)
  rw [p.card_U, p.cardB] at hcard
  have hle : (X ⊓ Subgroup.normalizer (Y : Set G)) ⊓ Subgroup.centralizer ({a} : Set G) ≤
      X ⊓ Subgroup.centralizer ({a} : Set G) := inf_le_inf_right _ inf_le_left
  have heq := Subgroup.eq_of_le_of_card_ge hle (by omega)
  rw [← heq]
  exact inf_le_left

theorem comm_mem_U (p : Pair626 X Y) {x a : G} (hx : x ∈ X)
    (ha : a ∈ Y ⊓ Subgroup.normalizer (X : Set G)) :
    x * a * x⁻¹ * a⁻¹ ∈ X ⊓ Subgroup.normalizer (Y : Set G) := by
  by_cases haB : a ∈ X ⊓ Y
  · have hxa : x * a = a * x := B2F.isElemAbelian_comm p.elemX hx haB.1
    have e : x * a * x⁻¹ * a⁻¹ = 1 := by rw [hxa]; group
    rw [e]
    exact Subgroup.one_mem _
  · apply p.centralizer_le_U ha haB
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr
      (comm_commute_ch626 p.elemX hx ha.2 (mul_self_eq_one_ch626 p.elemY ha.1))⟩
    have h1 : a * x⁻¹ * a⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp ha.2 _).mp (X.inv_mem hx)
    have e : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact X.mul_mem hx h1

theorem comm_not_mem_B (p : Pair626 X Y) {x a : G} (hx : x ∈ X)
    (hxU : x ∉ X ⊓ Subgroup.normalizer (Y : Set G))
    (ha : a ∈ Y ⊓ Subgroup.normalizer (X : Set G)) (haB : a ∉ X ⊓ Y) :
    x * a * x⁻¹ * a⁻¹ ∉ X ⊓ Y := by
  intro hxa
  have haC : a ∉ Subgroup.centralizer (X : Set G) := fun h => haB ⟨p.centA a ha h, ha.1⟩
  have h4 := p.fixX a ha haC
  have hall : ∀ y ∈ X, y * a * y⁻¹ * a⁻¹ ∈ X ⊓ Y := by
    intro y hy
    by_cases hyU : y ∈ X ⊓ Subgroup.normalizer (Y : Set G)
    · exact comm_mem_B' ha hyU
    · have hxy : x⁻¹ * y ∈ X ⊓ Subgroup.normalizer (Y : Set G) :=
        mul_mem_of_relIndex_two_ch626 p.idxU (X.inv_mem hx) hy
          (fun h => hxU (by simpa using (X ⊓ Subgroup.normalizer (Y : Set G)).inv_mem h)) hyU
      obtain ⟨u, hu, rfl⟩ : ∃ u ∈ X ⊓ Subgroup.normalizer (Y : Set G), x * u = y :=
        ⟨x⁻¹ * y, hxy, by group⟩
      have h1 := comm_mem_B' ha hu
      have hc : x * (u * a * u⁻¹ * a⁻¹) = (u * a * u⁻¹ * a⁻¹) * x :=
        B2F.isElemAbelian_comm p.elemX hx h1.1
      have e : x * u * a * (x * u)⁻¹ * a⁻¹ =
          (u * a * u⁻¹ * a⁻¹) * (x * a * x⁻¹ * a⁻¹) := by
        calc x * u * a * (x * u)⁻¹ * a⁻¹ = x * (u * a * u⁻¹ * a⁻¹) * a * x⁻¹ * a⁻¹ := by group
          _ = (u * a * u⁻¹ * a⁻¹) * x * a * x⁻¹ * a⁻¹ := by rw [hc]
          _ = _ := by group
      rw [e]
      exact (X ⊓ Y).mul_mem h1 hxa
  have h8 := card_le_mul_card_centralizer_ch626 (K := X) (B := X ⊓ Y) (a := a) hall
    (fun k hk b hb => B2F.isElemAbelian_comm p.elemX hk hb.1)
    (fun b hb b' hb' => B2F.isElemAbelian_comm p.elemX hb.1 hb'.1)
  rw [p.cardX, p.cardB] at h8
  omega

theorem exists_comm_comm_eq (p : Pair626 X Y) {v w u : G} (hv : v ∈ X)
    (hvU : v ∉ X ⊓ Subgroup.normalizer (Y : Set G)) (hw : w ∈ Y)
    (hwA : w ∉ Y ⊓ Subgroup.normalizer (X : Set G))
    (hu : u ∈ X ⊓ Subgroup.normalizer (Y : Set G)) :
    ∃ b ∈ X ⊓ Y, v * (w * u * w⁻¹ * u⁻¹) * v⁻¹ * (w * u * w⁻¹ * u⁻¹)⁻¹ = b * u := by
  obtain ⟨a, hadef⟩ : ∃ a, a = w * u * w⁻¹ * u⁻¹ := ⟨_, rfl⟩
  rw [← hadef]
  have ps := p.symm
  have ha : a ∈ Y ⊓ Subgroup.normalizer (X : Set G) := hadef ▸ ps.comm_mem_U hw hu
  by_cases huB : u ∈ X ⊓ Y
  · have hwu : w * u = u * w := B2F.isElemAbelian_comm p.elemY hw huB.2
    have ha1 : a = 1 := by rw [hadef, hwu]; group
    refine ⟨u⁻¹, (X ⊓ Y).inv_mem huB, ?_⟩
    rw [ha1]
    group
  · have haB : a ∉ X ⊓ Y := by
      have := ps.comm_not_mem_B hw hwA hu (by rwa [inf_comm])
      rw [inf_comm, ← hadef] at this
      exact this
    have hu' : v * a * v⁻¹ * a⁻¹ ∈ X ⊓ Subgroup.normalizer (Y : Set G) := p.comm_mem_U hv ha
    have hu'B : v * a * v⁻¹ * a⁻¹ ∉ X ⊓ Y := p.comm_not_mem_B hv hvU ha haB
    have haC : a ∉ Subgroup.centralizer (X : Set G) := fun h => haB ⟨p.centA a ha h, ha.1⟩
    have hS4 := p.fixX a ha haC
    have hBS : X ⊓ Y ≤ X ⊓ Subgroup.centralizer ({a} : Set G) := fun b hb =>
      ⟨hb.1, Subgroup.mem_centralizer_singleton_iff.mpr (B2F.isElemAbelian_comm p.elemY hb.2 ha.1)⟩
    have huS : u ∈ X ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine ⟨hu.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := comm_commute_ch626 p.elemY hw hu.2 (mul_self_eq_one_ch626 p.elemX hu.1)
      rw [← hadef] at this
      exact this.symm
    have hu'S : v * a * v⁻¹ * a⁻¹ ∈ X ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨hu'.1, Subgroup.mem_centralizer_singleton_iff.mpr
        (comm_commute_ch626 p.elemX hv ha.2 (mul_self_eq_one_ch626 p.elemY ha.1))⟩
    have hidx : (X ⊓ Y).relIndex (X ⊓ Subgroup.centralizer ({a} : Set G)) = 2 := by
      have h1 := Subgroup.relIndex_mul_card (H := X ⊓ Y)
        (K := X ⊓ Subgroup.centralizer ({a} : Set G))
      rw [inf_of_le_left hBS, p.cardB] at h1
      have hne : (X ⊓ Y).relIndex (X ⊓ Subgroup.centralizer ({a} : Set G)) ≠ 1 := fun h =>
        huB (Subgroup.relIndex_eq_one.mp h huS)
      have hpos : 0 < Nat.card ↥(X ⊓ Subgroup.centralizer ({a} : Set G)) := Nat.card_pos
      omega
    have huiB : u⁻¹ ∉ X ⊓ Y := fun h => huB (by simpa using (X ⊓ Y).inv_mem h)
    have hmem := mul_mem_of_relIndex_two_ch626 hidx hu'S
      ((X ⊓ Subgroup.centralizer ({a} : Set G)).inv_mem huS) hu'B huiB
    exact ⟨_, hmem, by group⟩

theorem conj_mem_A (p : Pair626 X Y) {v w u : G} (hv : v ∈ X)
    (hvU : v ∉ X ⊓ Subgroup.normalizer (Y : Set G)) (hw : w ∈ Y)
    (hwA : w ∉ Y ⊓ Subgroup.normalizer (X : Set G))
    (hu : u ∈ X ⊓ Subgroup.normalizer (Y : Set G)) :
    (v * w) * u * (v * w)⁻¹ ∈ Y ⊓ Subgroup.normalizer (X : Set G) := by
  obtain ⟨b, hb, hbu⟩ := p.exists_comm_comm_eq hv hvU hw hwA hu
  obtain ⟨a, hadef⟩ : ∃ a, a = w * u * w⁻¹ * u⁻¹ := ⟨_, rfl⟩
  rw [← hadef] at hbu
  have ha : a ∈ Y ⊓ Subgroup.normalizer (X : Set G) := hadef ▸ p.symm.comm_mem_U hw hu
  have hau : a * u = u * a := by
    have := comm_commute_ch626 p.elemY hw hu.2 (mul_self_eq_one_ch626 p.elemX hu.1)
    rwa [← hadef] at this
  have hvu : v * u = u * v := B2F.isElemAbelian_comm p.elemX hv hu.1
  have hu2 : u * u = 1 := mul_self_eq_one_ch626 p.elemX hu.1
  have e : (v * w) * u * (v * w)⁻¹ = b * a := by
    calc (v * w) * u * (v * w)⁻¹ = (v * a * v⁻¹ * a⁻¹) * a * (v * u * v⁻¹) := by
          rw [hadef]; group
      _ = (b * u) * a * (u * v * v⁻¹) := by rw [hbu, hvu]
      _ = b * (u * a) * u := by group
      _ = b * (a * u) * u := by rw [hau]
      _ = b * a * (u * u) := by group
      _ = b * a := by rw [hu2, mul_one]
  rw [e]
  exact (Y ⊓ Subgroup.normalizer (X : Set G)).mul_mem (B_le_A hb) ha

theorem conjSub_U_eq (p : Pair626 X Y) {v w : G} (hv : v ∈ X)
    (hvU : v ∉ X ⊓ Subgroup.normalizer (Y : Set G)) (hw : w ∈ Y)
    (hwA : w ∉ Y ⊓ Subgroup.normalizer (X : Set G)) :
    conjSub (v * w) (X ⊓ Subgroup.normalizer (Y : Set G)) =
      Y ⊓ Subgroup.normalizer (X : Set G) := by
  apply Subgroup.eq_of_le_of_card_ge
  · intro z hz
    rw [mem_conjSub] at hz
    have := p.conj_mem_A hv hvU hw hwA hz
    have e : (v * w) * ((v * w)⁻¹ * z * (v * w)) * (v * w)⁻¹ = z := by group
    rwa [e] at this
  · rw [CosetGeom.card_conjSub, p.card_A, p.card_U]

theorem conjSub_eq (p : Pair626 X Y) {v w : G} (hv : v ∈ X)
    (hvU : v ∉ X ⊓ Subgroup.normalizer (Y : Set G)) (hw : w ∈ Y)
    (hwA : w ∉ Y ⊓ Subgroup.normalizer (X : Set G)) : conjSub (v * w) X = Y := by
  obtain ⟨c, hc⟩ := p.conjXY
  have e : conjSub (v * w * c⁻¹) Y = conjSub (v * w) X := by
    rw [conjSub_mul, hc, conjSub_conjSub_inv]
  have h1 : Y ⊓ Subgroup.normalizer (X : Set G) ≤ conjSub (v * w * c⁻¹) Y := by
    rw [e, ← p.conjSub_U_eq hv hvU hw hwA]
    exact conjSub_mono _ inf_le_left
  have h2 := p.uniqY _ h1
  rwa [e] at h2

theorem pow_three_mem (p : Pair626 X Y) {v w : G} (hv : v ∈ X)
    (hvU : v ∉ X ⊓ Subgroup.normalizer (Y : Set G)) (hw : w ∈ Y)
    (hwA : w ∉ Y ⊓ Subgroup.normalizer (X : Set G)) :
    (v * w) ^ 3 ∈ Y ⊓ Subgroup.normalizer (X : Set G) := by
  have hX := p.conjSub_eq hv hvU hw hwA
  have hUA := p.conjSub_U_eq hv hvU hw hwA
  have h1 : (v * w) * v * (v * w)⁻¹ ∈ Y := by
    rw [← hX, mem_conjSub]
    have e : (v * w)⁻¹ * ((v * w) * v * (v * w)⁻¹) * (v * w) = v := by group
    rw [e]
    exact hv
  have h2 : (v * w) * v * (v * w)⁻¹ ∉ Y ⊓ Subgroup.normalizer (X : Set G) := by
    intro h
    rw [← hUA, mem_conjSub] at h
    apply hvU
    have e : (v * w)⁻¹ * ((v * w) * v * (v * w)⁻¹) * (v * w) = v := by group
    rwa [e] at h
  have h3 := mul_mem_of_relIndex_two_ch626 p.idxA h1 hw h2 hwA
  have hvi : v⁻¹ = v := inv_eq_self_ch626 p.elemX hv
  have hwi : w⁻¹ = w := inv_eq_self_ch626 p.elemY hw
  have e : (v * w) ^ 3 = (v * w) * v * (v * w)⁻¹ * w := by
    rw [mul_inv_rev, hvi, hwi, pow_three]
    group
  rw [e]
  exact h3

theorem commutator_eq (p : Pair626 X Y) :
    X ⊓ Y = ⁅Y ⊓ Subgroup.normalizer (X : Set G), X ⊓ Subgroup.normalizer (Y : Set G)⁆ := by
  have hle : ⁅Y ⊓ Subgroup.normalizer (X : Set G), X ⊓ Subgroup.normalizer (Y : Set G)⁆ ≤
      X ⊓ Y := by
    rw [Subgroup.commutator_le]
    intro a ha u hu
    rw [commutatorElement_def]
    exact comm_mem_B ha hu
  have hne : ⁅Y ⊓ Subgroup.normalizer (X : Set G), X ⊓ Subgroup.normalizer (Y : Set G)⁆ ≠ ⊥ := by
    intro h0
    have hAB : Y ⊓ Subgroup.normalizer (X : Set G) ≤ X ⊓ Y := by
      intro a ha
      refine p.mem_B_of_commute_U ha fun u hu => ?_
      have := Subgroup.commutator_mem_commutator ha hu
      rw [h0, Subgroup.mem_bot, commutatorElement_def] at this
      calc a * u = a * u * a⁻¹ * u⁻¹ * (u * a) := by group
        _ = u * a := by rw [this, one_mul]
    have := Subgroup.card_le_of_le hAB
    rw [p.card_A, p.cardB] at this
    omega
  have h2 : 2 ≤ Nat.card
      ↥(⁅Y ⊓ Subgroup.normalizer (X : Set G), X ⊓ Subgroup.normalizer (Y : Set G)⁆) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [p.cardB]; exact h2)).symm

end Pair626

end CFSG.Quasithin.H13
