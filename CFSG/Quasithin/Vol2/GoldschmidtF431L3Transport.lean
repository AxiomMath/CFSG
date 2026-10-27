module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpTrans
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

section Img

variable {X G : Type} [Group X] [Group G] {N : Subgroup X} (b : ↥N →* G)

theorem subgroupOf_inf' (Y Z N : Subgroup X) :
    (Y ⊓ Z).subgroupOf N = Y.subgroupOf N ⊓ Z.subgroupOf N := by
  ext x; simp [Subgroup.mem_subgroupOf]

theorem subgroupOf_map_subtype_self (Y : Subgroup N) : (Y.map N.subtype).subgroupOf N = Y := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.subtype_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  · intro hx; exact ⟨x, hx, rfl⟩

theorem subImg_inf' (hb : Function.Injective b) (Y Z : Subgroup X) :
    subImg b (Y ⊓ Z) = subImg b Y ⊓ subImg b Z := by
  unfold subImg
  rw [subgroupOf_inf', Subgroup.map_inf _ _ _ hb]

theorem subImg_le_range (Y : Subgroup X) : subImg b Y ≤ b.range := fun g hg => by
  obtain ⟨x, hx, -, rfl⟩ := mem_subImg.mp hg
  exact ⟨⟨x, hx⟩, rfl⟩

theorem card_subImg (hb : Function.Injective b) {Y : Subgroup X} (hY : Y ≤ N) :
    Nat.card (subImg b Y) = Nat.card Y := by
  unfold subImg
  rw [Subgroup.card_map_of_injective hb]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv

theorem subImg_injective (hb : Function.Injective b) {Y Z : Subgroup X} (hY : Y ≤ N) (hZ : Z ≤ N)
    (h : subImg b Y = subImg b Z) : Y = Z := by
  have h1 : Y.subgroupOf N = Z.subgroupOf N := Subgroup.map_injective hb h
  rw [← Subgroup.map_subgroupOf_eq_of_le hY, ← Subgroup.map_subgroupOf_eq_of_le hZ, h1]

theorem exists_pullback {A : Subgroup G} (hA : A ≤ b.range) : ∃ Y : Subgroup X, Y ≤ N ∧
    A = subImg b Y := by
  refine ⟨(A.comap b).map N.subtype, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩; exact y.2
  · unfold subImg
    rw [subgroupOf_map_subtype_self, Subgroup.map_comap_eq_self hA]

theorem subImg_conjSub (m : X) (hm : m ∈ N) (Y : Subgroup X) :
    conjSub (b ⟨m, hm⟩) (subImg b Y) = subImg b (conjSub m Y) := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    obtain ⟨y, hyN, hyY, hyx⟩ := mem_subImg.mp hx
    refine mem_subImg.mpr ⟨m * y * m⁻¹, N.mul_mem (N.mul_mem hm hyN) (N.inv_mem hm), ?_, ?_⟩
    · rw [mem_conjSub]; simpa [mul_assoc] using hyY
    · have : b ⟨m * y * m⁻¹, N.mul_mem (N.mul_mem hm hyN) (N.inv_mem hm)⟩ =
          b ⟨m, hm⟩ * b ⟨y, hyN⟩ * (b ⟨m, hm⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]; rfl
      rw [this, hyx]; group
  · intro hx
    obtain ⟨y, hyN, hyY, hyx⟩ := mem_subImg.mp hx
    rw [mem_conjSub] at hyY
    refine mem_subImg.mpr ⟨m⁻¹ * y * m, N.mul_mem (N.mul_mem (N.inv_mem hm) hyN) hm, hyY, ?_⟩
    have : b ⟨m⁻¹ * y * m, N.mul_mem (N.mul_mem (N.inv_mem hm) hyN) hm⟩ =
        (b ⟨m, hm⟩)⁻¹ * b ⟨y, hyN⟩ * b ⟨m, hm⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [this, hyx]

end Img


section ImgFrame

variable {X G : Type} [Group X] [Group G] {N : Subgroup X} (b : ↥N →* G)

theorem mem_subImg_apply (hb : Function.Injective b) {x : X} (hx : x ∈ N) {Y : Subgroup X} :
    b ⟨x, hx⟩ ∈ subImg b Y ↔ x ∈ Y := by
  constructor
  · intro h
    obtain ⟨y, hy, hyY, hyx⟩ := mem_subImg.mp h
    have : (⟨y, hy⟩ : ↥N) = ⟨x, hx⟩ := hb hyx
    have hyx' : y = x := congrArg Subtype.val this
    rwa [hyx'] at hyY
  · intro h
    exact mem_subImg_of_mem b hx h

theorem normedBy_subImg (hb : Function.Injective b) {B Y : Subgroup X} (hB : B ≤ N) (hY : Y ≤ N) :
    NormedBy (subImg b B) (subImg b Y) ↔ NormedBy B Y := by
  constructor
  · intro h x hx y hy
    have hxN : x ∈ N := hB hx
    have hyN : y ∈ N := hY hy
    have h1 := h (b ⟨x, hxN⟩) (mem_subImg_of_mem b hxN hx) (b ⟨y, hyN⟩)
      (mem_subImg_of_mem b hyN hy)
    have e : b ⟨x, hxN⟩ * b ⟨y, hyN⟩ * (b ⟨x, hxN⟩)⁻¹ =
        b ⟨x * y * x⁻¹, N.mul_mem (N.mul_mem hxN hyN) (N.inv_mem hxN)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e] at h1
    exact (mem_subImg_apply b hb _).mp h1
  · intro h g hg z hz
    obtain ⟨x, hxN, hxB, rfl⟩ := mem_subImg.mp hg
    obtain ⟨y, hyN, hyY, rfl⟩ := mem_subImg.mp hz
    have e : b ⟨x, hxN⟩ * b ⟨y, hyN⟩ * (b ⟨x, hxN⟩)⁻¹ =
        b ⟨x * y * x⁻¹, N.mul_mem (N.mul_mem hxN hyN) (N.inv_mem hxN)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]
    exact mem_subImg_of_mem b _ (h x hxB y hyY)

theorem Frame.transport {S Q₁ Q₂ : Subgroup X} (F : Frame S Q₁ Q₂) (hS : S ≤ N)
    (hb : Function.Injective b) : Frame (subImg b S) (subImg b Q₁) (subImg b Q₂) := by
  have h1 : Q₁ ≤ N := F.Q₁_le.trans hS
  have h2 : Q₂ ≤ N := F.Q₂_le.trans hS
  have hcS : centerOf (subImg b S) = subImg b (centerOf S) := subImg_centerOf hb hS
  have hea : ∀ {Q : Subgroup X}, Q ≤ N → IsElemAbelian 2 Q → IsElemAbelian 2 (subImg b Q) := by
    intro Q hQ hQe
    rw [F7.isElemAbelian_iff]
    refine ⟨?_, ?_⟩
    · intro x hx y hy
      obtain ⟨x', hx', hxQ, rfl⟩ := mem_subImg.mp hx
      obtain ⟨y', hy', hyQ, rfl⟩ := mem_subImg.mp hy
      exact (commute_iff_of_injective hb hy' hx').mpr (F7.isElemAbelian_comm hQe hxQ hyQ)
    · intro x hx
      obtain ⟨x', hx', hxQ, rfl⟩ := mem_subImg.mp hx
      exact (sq_eq_one_iff_of_injective hb hx').mpr (F7.isElemAbelian_pow_eq_one hQe hxQ)
  refine ⟨subImg_mono b F.Q₁_le, subImg_mono b F.Q₂_le, hea h1 F.Q₁_ea, hea h2 F.Q₂_ea, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcS, ← subImg_inf' b hb, F.inter]
  · rw [card_subImg b hb h1, card_subImg b hb h2]; exact F.card_eq
  · rw [card_subImg b hb h1]; exact F.four_le
  · intro h; exact F.Q_ne (subImg_injective b hb h1 h2 h)
  · intro x hx y hy
    obtain ⟨x', hx', hxS, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy', hyS, rfl⟩ := mem_subImg.mp hy
    have hc := F.comm x' hxS y' hyS
    rw [hcS]
    have e : b ⟨x', hx'⟩ * b ⟨y', hy'⟩ * (b ⟨x', hx'⟩)⁻¹ * (b ⟨y', hy'⟩)⁻¹ =
        b ⟨x' * y' * x'⁻¹ * y'⁻¹,
          N.mul_mem (N.mul_mem (N.mul_mem hx' hy') (N.inv_mem hx')) (N.inv_mem hy')⟩ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]; rfl
    rw [e]
    exact mem_subImg_of_mem b _ hc
  · intro x hx hx2 hx1
    obtain ⟨x', hx', hxS, rfl⟩ := mem_subImg.mp hx
    have hx2' : x' ^ 2 = 1 := (sq_eq_one_iff_of_injective hb hx').mp hx2
    have hx1' : x' ≠ 1 := by
      rintro rfl; exact hx1 (map_one b)
    rcases F.inv x' hxS hx2' hx1' with h | h
    · exact Or.inl (mem_subImg_of_mem b hx' h)
    · exact Or.inr (mem_subImg_of_mem b hx' h)
  · intro x hx hxZ y hy hxy
    obtain ⟨x', hx', hxQ, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy', hyS, rfl⟩ := mem_subImg.mp hy
    rw [hcS] at hxZ
    have hxZ' : x' ∉ centerOf S := fun h => hxZ (mem_subImg_of_mem b hx' h)
    exact mem_subImg_of_mem b hy' (F.cent₁ x' hxQ hxZ' y' hyS
      ((commute_iff_of_injective hb hx' hy').mp hxy))
  · intro x hx hxZ y hy hxy
    obtain ⟨x', hx', hxQ, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy', hyS, rfl⟩ := mem_subImg.mp hy
    rw [hcS] at hxZ
    have hxZ' : x' ∉ centerOf S := fun h => hxZ (mem_subImg_of_mem b hx' h)
    exact mem_subImg_of_mem b hy' (F.cent₂ x' hxQ hxZ' y' hyS
      ((commute_iff_of_injective hb hx' hy').mp hxy))
  · intro A hA hAe hcard
    obtain ⟨Y, hYN, rfl⟩ := exists_pullback b (hA.trans (subImg_le_range b S))
    have hYS : Y ≤ S := by
      intro x hx
      have hxN := hYN hx
      have : b ⟨x, hxN⟩ ∈ subImg b S := hA (mem_subImg_of_mem b hxN hx)
      exact (mem_subImg_apply b hb hxN).mp this
    have hYea : IsElemAbelian 2 Y := by
      rw [F7.isElemAbelian_iff]
      refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
      · have hxN := hYN hx
        have hyN := hYN hy
        have := F7.isElemAbelian_comm hAe (mem_subImg_of_mem b hxN hx) (mem_subImg_of_mem b hyN hy)
        exact (commute_iff_of_injective hb hyN hxN).mp this
      · have hxN := hYN hx
        exact (sq_eq_one_iff_of_injective hb hxN).mp
          (F7.isElemAbelian_pow_eq_one hAe (mem_subImg_of_mem b hxN hx))
    have hcard' : Nat.card Q₁ ≤ Nat.card Y := by
      rw [card_subImg b hb h1] at hcard
      rwa [card_subImg b hb hYN] at hcard
    rcases F.maxea Y hYS hYea hcard' with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])

end ImgFrame

structure AmalgIso {X G : Type} [Group X] [Group G] (N₁ N₂ : Subgroup X)
    (M₁ M₂ : Subgroup G) where
  b₁ : ↥N₁ →* G
  b₂ : ↥N₂ →* G
  inj₁ : Function.Injective b₁
  inj₂ : Function.Injective b₂
  agree : ∀ g (h1 : g ∈ N₁) (h2 : g ∈ N₂), b₁ ⟨g, h1⟩ = b₂ ⟨g, h2⟩
  range₁ : b₁.range = M₁
  range₂ : b₂.range = M₂
  inter : ∀ x ∈ M₁ ⊓ M₂, ∃ (g : X) (h1 : g ∈ N₁) (_ : g ∈ N₂), b₁ ⟨g, h1⟩ = x

namespace AmalgIso

variable {X G : Type} [Group X] [Group G] {N₁ N₂ : Subgroup X} {M₁ M₂ : Subgroup G}
  (T : AmalgIso N₁ N₂ M₁ M₂)

theorem mem_M₁ {x : G} : x ∈ M₁ ↔ ∃ (g : X) (h : g ∈ N₁), T.b₁ ⟨g, h⟩ = x := by
  have h := T.range₁
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨⟨g, h'⟩, rfl⟩ := hx
    exact ⟨g, h', rfl⟩
  · rintro ⟨g, h', rfl⟩
    have : T.b₁ ⟨g, h'⟩ ∈ T.b₁.range := ⟨⟨g, h'⟩, rfl⟩
    rwa [h] at this

theorem mem_M₂ {x : G} : x ∈ M₂ ↔ ∃ (g : X) (h : g ∈ N₂), T.b₂ ⟨g, h⟩ = x := by
  have h := T.range₂
  constructor
  · intro hx
    rw [← h] at hx
    obtain ⟨⟨g, h'⟩, rfl⟩ := hx
    exact ⟨g, h', rfl⟩
  · rintro ⟨g, h', rfl⟩
    have : T.b₂ ⟨g, h'⟩ ∈ T.b₂.range := ⟨⟨g, h'⟩, rfl⟩
    rwa [h] at this

theorem mem_H {x : G} :
    x ∈ M₁ ⊓ M₂ ↔ ∃ (g : X) (h1 : g ∈ N₁) (_ : g ∈ N₂), T.b₁ ⟨g, h1⟩ = x := by
  constructor
  · exact T.inter x
  · rintro ⟨g, h1, h2, rfl⟩
    exact ⟨T.mem_M₁.mpr ⟨g, h1, rfl⟩, T.mem_M₂.mpr ⟨g, h2, (T.agree g h1 h2).symm⟩⟩

end AmalgIso


section Main

variable {X G : Type} [Group X] [Group G] {N₁ N₂ : Subgroup X} {M₁ M₂ : Subgroup G}

theorem L3Datum.nonempty_transport (D : L3Datum N₁ N₂) (T : AmalgIso N₁ N₂ M₁ M₂) :
    Nonempty (L3Datum M₁ M₂) := by
  have hSH : D.S ≤ N₁ ⊓ N₂ := D.S_le_H
  have hS1 : D.S ≤ N₁ := hSH.trans inf_le_left
  have hB1 : D.B ≤ N₁ := D.B_le.trans inf_le_left
  have hQ1 : D.Q₁ ≤ N₁ := D.frame.Q₁_le.trans hS1
  have hQ2 : D.Q₂ ≤ N₁ := D.frame.Q₂_le.trans hS1
  have hZ1 : centerOf D.S ≤ N₁ := inf_le_left.trans hS1
  have hb := T.inj₁
  have hcS : centerOf (subImg T.b₁ D.S) = subImg T.b₁ (centerOf D.S) := subImg_centerOf hb hS1
  refine ⟨
    { S := subImg T.b₁ D.S
      B := subImg T.b₁ D.B
      Q₁ := subImg T.b₁ D.Q₁
      Q₂ := subImg T.b₁ D.Q₂
      s₁ := T.b₁ ⟨D.s₁, D.s₁_mem⟩
      s₂ := T.b₂ ⟨D.s₂, D.s₂_mem⟩
      S_eq := ?_
      B_le := ?_
      B_odd := ?_
      mul_SB := ?_
      S_index := ?_
      frame := D.frame.transport T.b₁ hS1 hb
      Q₁_norm := ?_
      Q₂_norm := ?_
      trans := ?_
      cent := ?_
      cov₁ := ?_
      cov₂ := ?_
      nonsolv := ?_
      s₁_mem := ?_
      s₁_not := ?_
      s₁_sq := ?_
      s₁_norm := ?_
      s₂_mem := ?_
      s₂_not := ?_
      s₂_sq := ?_
      s₂_norm := ?_
      fix₁ := ?_
      fix₂ := ?_
      centS := ?_
      Z_big := ?_
      rot := ?_ }⟩
  ·
    have e1 : M₁ ⊓ M₂ = subImg T.b₁ (N₁ ⊓ N₂) := by
      ext x
      rw [T.mem_H, mem_subImg]
      constructor
      · rintro ⟨g, h1, h2, rfl⟩; exact ⟨g, h1, ⟨h1, h2⟩, rfl⟩
      · rintro ⟨g, h1, ⟨h1', h2⟩, rfl⟩; exact ⟨g, h1, h2, rfl⟩
    rw [e1, subImg_pCoreOf hb inf_le_left, ← D.S_eq]
  ·
    intro g hg
    obtain ⟨x, hx, hxB, rfl⟩ := mem_subImg.mp hg
    exact T.mem_H.mpr ⟨x, hx, (D.B_le hxB).2, rfl⟩
  ·
    rw [card_subImg T.b₁ hb hB1]; exact D.B_odd
  ·
    intro h hh
    obtain ⟨g, h1, h2, rfl⟩ := T.mem_H.mp hh
    obtain ⟨s, hs, b, hb', hg⟩ := D.mul_SB g ⟨h1, h2⟩
    have hsN : s ∈ N₁ := hS1 hs
    have hbN : b ∈ N₁ := hB1 hb'
    refine ⟨T.b₁ ⟨s, hsN⟩, mem_subImg_of_mem _ hsN hs, T.b₁ ⟨b, hbN⟩, mem_subImg_of_mem _ hbN hb',
      ?_⟩
    rw [← map_mul]
    congr 1
    exact Subtype.ext hg
  ·
    have h1 : (subImg T.b₁ D.S).relIndex T.b₁.range = (D.S.subgroupOf N₁).relIndex ⊤ := by
      unfold subImg
      rw [MonoidHom.range_eq_map]
      exact Subgroup.relIndex_map_map_of_injective _ _ hb
    rw [Subgroup.relIndex_top_right, T.range₁] at h1
    rw [h1]; exact D.S_index
  ·
    intro m hm x hx
    obtain ⟨m', hm', rfl⟩ := T.mem_M₁.mp hm
    obtain ⟨x', hx', hxQ, rfl⟩ := mem_subImg.mp hx
    have hq := D.Q₁_norm m' hm' x' hxQ
    have e : T.b₁ ⟨m', hm'⟩ * T.b₁ ⟨x', hx'⟩ * (T.b₁ ⟨m', hm'⟩)⁻¹ =
        T.b₁ ⟨m' * x' * m'⁻¹, N₁.mul_mem (N₁.mul_mem hm' hx') (N₁.inv_mem hm')⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]; exact mem_subImg_of_mem _ _ hq
  ·
    intro m hm x hx
    obtain ⟨m', hm', rfl⟩ := T.mem_M₂.mp hm
    obtain ⟨x', hx', hxQ, rfl⟩ := mem_subImg.mp hx
    have hx2 : x' ∈ N₂ := (hSH (D.frame.Q₂_le hxQ)).2
    have hq := D.Q₂_norm m' hm' x' hxQ
    have hq1 : m' * x' * m'⁻¹ ∈ N₁ := hQ2 hq
    have hq2 : m' * x' * m'⁻¹ ∈ N₂ := N₂.mul_mem (N₂.mul_mem hm' hx2) (N₂.inv_mem hm')
    have e : T.b₂ ⟨m', hm'⟩ * T.b₁ ⟨x', hx'⟩ * (T.b₂ ⟨m', hm'⟩)⁻¹ =
        T.b₁ ⟨m' * x' * m'⁻¹, hq1⟩ := by
      rw [T.agree x' hx' hx2, T.agree _ hq1 hq2, ← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]; exact mem_subImg_of_mem _ _ hq
  ·
    intro x hx hx1 y hy hy1
    rw [hcS] at hx hy
    obtain ⟨x', hx', hxZ, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy', hyZ, rfl⟩ := mem_subImg.mp hy
    have hx1' : x' ≠ 1 := by rintro rfl; exact hx1 (map_one T.b₁)
    have hy1' : y' ≠ 1 := by rintro rfl; exact hy1 (map_one T.b₁)
    obtain ⟨c, hc, hcxy⟩ := D.trans x' hxZ hx1' y' hyZ hy1'
    have hcN : c ∈ N₁ := hB1 hc
    refine ⟨T.b₁ ⟨c, hcN⟩, mem_subImg_of_mem _ hcN hc, ?_⟩
    have e : T.b₁ ⟨c, hcN⟩ * T.b₁ ⟨x', hx'⟩ * (T.b₁ ⟨c, hcN⟩)⁻¹ =
        T.b₁ ⟨c * x' * c⁻¹, N₁.mul_mem (N₁.mul_mem hcN hx') (N₁.inv_mem hcN)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]; congr 1; exact Subtype.ext hcxy
  ·
    intro x hx hx1 y hy hxy
    rw [hcS] at hx
    obtain ⟨x', hx', hxZ, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy', rfl⟩ := T.mem_M₁.mp hy
    have hx1' : x' ≠ 1 := by rintro rfl; exact hx1 (map_one T.b₁)
    have hcomm : y' * x' = x' * y' := (commute_iff_of_injective hb hx' hy').mp hxy
    have hy2 : y' ∈ N₂ := D.cent x' hxZ hx1' y' hy' hcomm
    exact T.mem_M₂.mpr ⟨y', hy2, (T.agree y' hy' hy2).symm⟩
  ·
    intro x hx hx1
    obtain ⟨x', hx', hxQ, rfl⟩ := mem_subImg.mp hx
    have hx1' : x' ≠ 1 := by rintro rfl; exact hx1 (map_one T.b₁)
    obtain ⟨m, hm, hmZ⟩ := D.cov₁ x' hxQ hx1'
    refine ⟨T.b₁ ⟨m, hm⟩, T.mem_M₁.mpr ⟨m, hm, rfl⟩, ?_⟩
    rw [hcS]
    have e : T.b₁ ⟨m, hm⟩ * T.b₁ ⟨x', hx'⟩ * (T.b₁ ⟨m, hm⟩)⁻¹ =
        T.b₁ ⟨m * x' * m⁻¹, N₁.mul_mem (N₁.mul_mem hm hx') (N₁.inv_mem hm)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]; exact mem_subImg_of_mem _ _ hmZ
  ·
    intro x hx hx1
    obtain ⟨x', hx', hxQ, rfl⟩ := mem_subImg.mp hx
    have hx1' : x' ≠ 1 := by rintro rfl; exact hx1 (map_one T.b₁)
    have hx2 : x' ∈ N₂ := (hSH (D.frame.Q₂_le hxQ)).2
    obtain ⟨m, hm, hmZ⟩ := D.cov₂ x' hxQ hx1'
    have hq1 : m * x' * m⁻¹ ∈ N₁ := hZ1 hmZ
    have hq2 : m * x' * m⁻¹ ∈ N₂ := N₂.mul_mem (N₂.mul_mem hm hx2) (N₂.inv_mem hm)
    refine ⟨T.b₂ ⟨m, hm⟩, T.mem_M₂.mpr ⟨m, hm, rfl⟩, ?_⟩
    rw [hcS]
    have e : T.b₂ ⟨m, hm⟩ * T.b₁ ⟨x', hx'⟩ * (T.b₂ ⟨m, hm⟩)⁻¹ = T.b₁ ⟨m * x' * m⁻¹, hq1⟩ := by
      rw [T.agree x' hx' hx2, T.agree _ hq1 hq2, ← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]; exact mem_subImg_of_mem _ _ hmZ
  ·
    intro hsolv
    apply D.nonsolv
    let f : ↥N₁ →* ↥M₁ := T.b₁.codRestrict M₁ (fun x => T.mem_M₁.mpr ⟨x.1, x.2, rfl⟩)
    have hf : Function.Injective f := fun a c h => hb (congrArg Subtype.val h)
    exact Group.isSolvable_of_isSolvable_injective hf
  · exact T.mem_M₁.mpr ⟨_, _, rfl⟩
  ·
    intro h2
    have hH : T.b₁ ⟨D.s₁, D.s₁_mem⟩ ∈ M₁ ⊓ M₂ := ⟨T.mem_M₁.mpr ⟨_, _, rfl⟩, h2⟩
    obtain ⟨g, h1, h2', hg⟩ := T.mem_H.mp hH
    have : (⟨g, h1⟩ : ↥N₁) = ⟨D.s₁, D.s₁_mem⟩ := hb hg
    have hgs : g = D.s₁ := congrArg Subtype.val this
    exact D.s₁_not (hgs ▸ h2')
  ·
    rw [← map_mul]
    have : (⟨D.s₁, D.s₁_mem⟩ * ⟨D.s₁, D.s₁_mem⟩ : ↥N₁) = 1 := Subtype.ext D.s₁_sq
    rw [this, map_one]
  ·
    intro b hbm
    obtain ⟨b', hb'N, hb'B, rfl⟩ := mem_subImg.mp hbm
    have hq := D.s₁_norm b' hb'B
    have e : T.b₁ ⟨D.s₁, D.s₁_mem⟩ * T.b₁ ⟨b', hb'N⟩ * (T.b₁ ⟨D.s₁, D.s₁_mem⟩)⁻¹ =
        T.b₁ ⟨D.s₁ * b' * D.s₁⁻¹, N₁.mul_mem (N₁.mul_mem D.s₁_mem hb'N) (N₁.inv_mem D.s₁_mem)⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]; exact mem_subImg_of_mem _ _ hq
  · exact T.mem_M₂.mpr ⟨_, _, rfl⟩
  ·
    intro h1
    have hH : T.b₂ ⟨D.s₂, D.s₂_mem⟩ ∈ M₁ ⊓ M₂ := ⟨h1, T.mem_M₂.mpr ⟨_, _, rfl⟩⟩
    obtain ⟨g, hg1, hg2, hg⟩ := T.mem_H.mp hH
    have hg' : T.b₂ ⟨g, hg2⟩ = T.b₂ ⟨D.s₂, D.s₂_mem⟩ := by rw [← T.agree g hg1 hg2]; exact hg
    have : (⟨g, hg2⟩ : ↥N₂) = ⟨D.s₂, D.s₂_mem⟩ := T.inj₂ hg'
    have hgs : g = D.s₂ := congrArg Subtype.val this
    exact D.s₂_not (hgs ▸ hg1)
  ·
    rw [← map_mul]
    have : (⟨D.s₂, D.s₂_mem⟩ * ⟨D.s₂, D.s₂_mem⟩ : ↥N₂) = 1 := Subtype.ext D.s₂_sq
    rw [this, map_one]
  ·
    intro b hbm
    obtain ⟨b', hb'N, hb'B, rfl⟩ := mem_subImg.mp hbm
    have hb'2 : b' ∈ N₂ := (D.B_le hb'B).2
    have hq := D.s₂_norm b' hb'B
    have hq1 : D.s₂ * b' * D.s₂⁻¹ ∈ N₁ := hB1 hq
    have hq2 : D.s₂ * b' * D.s₂⁻¹ ∈ N₂ :=
      N₂.mul_mem (N₂.mul_mem D.s₂_mem hb'2) (N₂.inv_mem D.s₂_mem)
    have e : T.b₂ ⟨D.s₂, D.s₂_mem⟩ * T.b₁ ⟨b', hb'N⟩ * (T.b₂ ⟨D.s₂, D.s₂_mem⟩)⁻¹ =
        T.b₁ ⟨D.s₂ * b' * D.s₂⁻¹, hq1⟩ := by
      rw [T.agree b' hb'N hb'2, T.agree _ hq1 hq2, ← map_inv, ← map_mul, ← map_mul]; rfl
    rw [e]; exact mem_subImg_of_mem _ _ hq
  ·
    intro m hm hmB
    obtain ⟨m', hm', rfl⟩ := T.mem_M₁.mp hm
    rw [hcS] at hmB ⊢
    rw [subImg_conjSub T.b₁ m' hm' (centerOf D.S)] at hmB ⊢
    have hY0 : conjSub m' (centerOf D.S) ≤ N₁ := by
      intro x hx
      have := hZ1 (mem_conjSub.mp hx)
      have h2 := N₁.mul_mem (N₁.mul_mem hm' this) (N₁.inv_mem hm')
      simpa [mul_assoc] using h2
    have hn : NormedBy D.B (conjSub m' (centerOf D.S)) :=
      (normedBy_subImg T.b₁ hb hB1 hY0).mp hmB
    rw [subImg_conjSub T.b₁ D.s₁ D.s₁_mem (centerOf D.S)]
    rcases D.fix₁ m' hm' hn with h | h
    · left; rw [h]
    · right; rw [h]
  ·
    intro m hm hmB
    obtain ⟨m', hm', rfl⟩ := T.mem_M₂.mp hm
    have hZ2 : centerOf D.S ≤ N₂ := inf_le_left.trans (hSH.trans inf_le_right)
    have hB2 : D.B ≤ N₂ := D.B_le.trans inf_le_right
    have eZ : subImg T.b₁ (centerOf D.S) = subImg T.b₂ (centerOf D.S) :=
      subImg_eq_of_agree T.agree hZ1 hZ2
    have eB : subImg T.b₁ D.B = subImg T.b₂ D.B := subImg_eq_of_agree T.agree hB1 hB2
    rw [hcS, eZ] at hmB ⊢
    rw [eB] at hmB
    rw [subImg_conjSub T.b₂ m' hm' (centerOf D.S)] at hmB ⊢
    have hY0 : conjSub m' (centerOf D.S) ≤ N₂ := by
      intro x hx
      have := hZ2 (mem_conjSub.mp hx)
      have h2 := N₂.mul_mem (N₂.mul_mem hm' this) (N₂.inv_mem hm')
      simpa [mul_assoc] using h2
    have hn : NormedBy D.B (conjSub m' (centerOf D.S)) :=
      (normedBy_subImg T.b₂ T.inj₂ hB2 hY0).mp hmB
    rw [subImg_conjSub T.b₂ D.s₂ D.s₂_mem (centerOf D.S)]
    rcases D.fix₂ m' hm' hn with h | h
    · left; rw [h]
    · right; rw [h]
  ·
    intro x hx hc
    obtain ⟨x', hx', hxS, rfl⟩ := mem_subImg.mp hx
    have : x' = 1 := D.centS x' hxS (fun b hbB => by
      have hbN := hB1 hbB
      exact (commute_iff_of_injective hb hbN hx').mp (hc _ (mem_subImg_of_mem _ hbN hbB)))
    subst this
    exact map_one T.b₁
  ·
    obtain ⟨x, hx, y, hy, hx1, hy1, hne⟩ := D.Z_big
    have hxN : x ∈ N₁ := hZ1 hx
    have hyN : y ∈ N₁ := hZ1 hy
    refine ⟨T.b₁ ⟨x, hxN⟩, ?_, T.b₁ ⟨y, hyN⟩, ?_, ?_, ?_, ?_⟩
    · rw [hcS]; exact mem_subImg_of_mem _ hxN hx
    · rw [hcS]; exact mem_subImg_of_mem _ hyN hy
    · intro h; apply hx1
      have := hb (h.trans (map_one T.b₁).symm)
      exact congrArg Subtype.val this
    · intro h; apply hy1
      have := hb (h.trans (map_one T.b₁).symm)
      exact congrArg Subtype.val this
    · intro h; apply hne
      have := hb h
      exact congrArg Subtype.val this
  ·
    obtain ⟨b₃, hb₃, hrot⟩ := D.rot
    have hb₃N : b₃ ∈ N₁ := hB1 hb₃
    refine ⟨T.b₁ ⟨b₃, hb₃N⟩, mem_subImg_of_mem _ hb₃N hb₃, ?_⟩
    intro x hx
    obtain ⟨x₀, hx₀N, hx₀B, rfl⟩ := mem_subImg.mp hx
    have step₁ : ∀ y : X, ∀ hy : y ∈ D.B, ∃ hz : D.s₁ * y * D.s₁⁻¹ ∈ D.B,
        T.b₁ ⟨D.s₁, D.s₁_mem⟩ * T.b₁ ⟨y, hB1 hy⟩ * (T.b₁ ⟨D.s₁, D.s₁_mem⟩)⁻¹ =
          T.b₁ ⟨D.s₁ * y * D.s₁⁻¹, hB1 hz⟩ := by
      intro y hy
      refine ⟨D.s₁_norm y hy, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]; rfl
    have step₂ : ∀ y : X, ∀ hy : y ∈ D.B, ∃ hz : D.s₂ * y * D.s₂⁻¹ ∈ D.B,
        T.b₂ ⟨D.s₂, D.s₂_mem⟩ * T.b₁ ⟨y, hB1 hy⟩ * (T.b₂ ⟨D.s₂, D.s₂_mem⟩)⁻¹ =
          T.b₁ ⟨D.s₂ * y * D.s₂⁻¹, hB1 hz⟩ := by
      intro y hy
      have hy2 : y ∈ N₂ := (D.B_le hy).2
      have hz := D.s₂_norm y hy
      have hz2 : D.s₂ * y * D.s₂⁻¹ ∈ N₂ :=
        N₂.mul_mem (N₂.mul_mem D.s₂_mem hy2) (N₂.inv_mem D.s₂_mem)
      refine ⟨hz, ?_⟩
      rw [T.agree y (hB1 hy) hy2, T.agree _ (hB1 hz) hz2, ← map_inv, ← map_mul, ← map_mul]; rfl
    obtain ⟨h1, e1⟩ := step₂ x₀ hx₀B
    obtain ⟨h2, e2⟩ := step₁ _ h1
    obtain ⟨h3, e3⟩ := step₂ _ h2
    obtain ⟨h4, e4⟩ := step₁ _ h3
    obtain ⟨h5, e5⟩ := step₂ _ h4
    obtain ⟨h6, e6⟩ := step₁ _ h5
    have hX := hrot x₀ hx₀B
    have hnest : D.s₁ * (D.s₂ * (D.s₁ * (D.s₂ * (D.s₁ * (D.s₂ * x₀ * D.s₂⁻¹) * D.s₁⁻¹) *
        D.s₂⁻¹) * D.s₁⁻¹) * D.s₂⁻¹) * D.s₁⁻¹ = b₃ * x₀ * b₃⁻¹ := by
      rw [← hX, pow_three']; group
    have hG : (T.b₁ ⟨D.s₁, D.s₁_mem⟩ * T.b₂ ⟨D.s₂, D.s₂_mem⟩) ^ 3 * T.b₁ ⟨x₀, hx₀N⟩ *
        ((T.b₁ ⟨D.s₁, D.s₁_mem⟩ * T.b₂ ⟨D.s₂, D.s₂_mem⟩) ^ 3)⁻¹ =
        T.b₁ ⟨D.s₁ * (D.s₂ * (D.s₁ * (D.s₂ * (D.s₁ * (D.s₂ * x₀ * D.s₂⁻¹) * D.s₁⁻¹) *
          D.s₂⁻¹) * D.s₁⁻¹) * D.s₂⁻¹) * D.s₁⁻¹, hB1 h6⟩ := by
      rw [← e6, ← e5, ← e4, ← e3, ← e2, ← e1, pow_three']
      group
    rw [hG]
    have hsub : (⟨D.s₁ * (D.s₂ * (D.s₁ * (D.s₂ * (D.s₁ * (D.s₂ * x₀ * D.s₂⁻¹) * D.s₁⁻¹) *
          D.s₂⁻¹) * D.s₁⁻¹) * D.s₂⁻¹) * D.s₁⁻¹, hB1 h6⟩ : ↥N₁) =
        ⟨b₃ * x₀ * b₃⁻¹, N₁.mul_mem (N₁.mul_mem hb₃N hx₀N) (N₁.inv_mem hb₃N)⟩ :=
      Subtype.ext hnest
    rw [hsub, ← map_inv, ← map_mul, ← map_mul]
    rfl

end Main


end CFSG.Quasithin.H13.F431.L3

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin.H13.F431.L3

theorem LieExt.inter {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G}
    (E : LieExt D M1 M2) :
    ∀ x ∈ M1 ⊓ M2, ∃ (g : ↥E.K) (h1 : g ∈ E.Mb1) (_ : g ∈ E.Mb2), E.b1 ⟨g, h1⟩ = x := by
  intro x hx
  have ha1 : ((E.phi12 ⟨x, hx⟩ : ↥(E.N1 ⊓ E.N2)) : MulAut D) ∈ E.N1 := (E.phi12 ⟨x, hx⟩).2.1
  have ha2 : ((E.phi12 ⟨x, hx⟩ : ↥(E.N1 ⊓ E.N2)) : MulAut D) ∈ E.N2 := (E.phi12 ⟨x, hx⟩).2.2
  have hg1 : (⟨((E.phi12 ⟨x, hx⟩ : ↥(E.N1 ⊓ E.N2)) : MulAut D), E.N1_le_K ha1⟩ : ↥E.K) ∈ E.Mb1 :=
    Subgroup.mem_subgroupOf.mpr ha1
  have hg2 : (⟨((E.phi12 ⟨x, hx⟩ : ↥(E.N1 ⊓ E.N2)) : MulAut D), E.N1_le_K ha1⟩ : ↥E.K) ∈ E.Mb2 :=
    Subgroup.mem_subgroupOf.mpr ha2
  refine ⟨_, hg1, hg2, ?_⟩
  rw [E.b1_apply _ hg1]
  have : E.phi1.symm ⟨((E.phi12 ⟨x, hx⟩ : ↥(E.N1 ⊓ E.N2)) : MulAut D), ha1⟩ = ⟨x, hx.1⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext (E.phi1_phi12 ⟨x, hx⟩).symm
  exact congrArg Subtype.val this

noncomputable def LieExt.amalgIso {D : Type} [Group D] {G : Type} [Group G] {M1 M2 : Subgroup G}
    (E : LieExt D M1 M2) : AmalgIso E.Mb1 E.Mb2 M1 M2 where
  b₁ := E.b1
  b₂ := E.b2
  inj₁ := E.comp.inj₁
  inj₂ := E.comp.inj₂
  agree := E.comp.agree
  range₁ := E.range_b1
  range₂ := E.range_b2
  inter := E.inter

end CFSG.Quasithin.H13.F431
