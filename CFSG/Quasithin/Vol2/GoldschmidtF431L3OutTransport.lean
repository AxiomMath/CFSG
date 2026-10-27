module

public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Transport
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Out

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

section Img2

variable {X G : Type} [Group X] [Group G] {N : Subgroup X} (b : ↥N →* G)

theorem relIndex_subImg_range (hb : Function.Injective b) (Y : Subgroup X) :
    (subImg b Y).relIndex b.range = Y.relIndex N := by
  unfold subImg
  rw [MonoidHom.range_eq_map]
  have := Subgroup.relIndex_map_map_of_injective (Y.subgroupOf N) ⊤ hb
  rw [Subgroup.relIndex_top_right] at this
  rw [this]
  rfl

theorem isPGroup_subImg (hb : Function.Injective b) {Y : Subgroup X} (hY : Y ≤ N)
    (hp : IsPGroup 2 Y) : IsPGroup 2 (subImg b Y) := by
  have hp1 : IsPGroup 2 (Y.subgroupOf N) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hY).symm
  exact hp1.of_equiv (Subgroup.equivMapOfInjective _ b hb)

theorem subImg_inf_centralizer (hb : Function.Injective b) {f : X} (hf : f ∈ N) (Y : Subgroup X) :
    subImg b (Y ⊓ Subgroup.centralizer ({f} : Set X)) =
      subImg b Y ⊓ Subgroup.centralizer ({b ⟨f, hf⟩} : Set G) := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hxN, hx, rfl⟩ := mem_subImg.mp hg
    obtain ⟨hxY, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨mem_subImg_of_mem b hxN hxY, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_iff_of_injective hb hf hxN).mpr (Subgroup.mem_centralizer_singleton_iff.mp hxc)
  · intro hg
    obtain ⟨hg1, hgc⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨x, hxN, hxY, rfl⟩ := mem_subImg.mp hg1
    refine mem_subImg_of_mem b hxN (Subgroup.mem_inf.mpr ⟨hxY, ?_⟩)
    rw [Subgroup.mem_centralizer_singleton_iff] at hgc ⊢
    exact (commute_iff_of_injective hb hf hxN).mp hgc

theorem subImg_bot : subImg b (⊥ : Subgroup X) = ⊥ := by
  unfold subImg
  rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]

theorem subImg_commutator {Y : Subgroup X} (hY : Y ≤ N) :
    subImg b ⁅Y, Y⁆ = ⁅subImg b Y, subImg b Y⁆ := by
  have h1 : ⁅Y, Y⁆ = ⁅Y.subgroupOf N, Y.subgroupOf N⁆.map N.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hY]
  unfold subImg
  rw [h1, subgroupOf_map_subtype_self, ← Subgroup.map_commutator]

theorem isSylowTwoOf_subImg (hb : Function.Injective b) {X' Y : Subgroup X} (hY : Y ≤ N)
    (h : IsSylowTwoOf X' Y) : IsSylowTwoOf (subImg b X') (subImg b Y) := by
  have hX'N : X' ≤ N := h.1.trans hY
  refine ⟨subImg_mono b h.1, isPGroup_subImg b hb hX'N h.2.1, ?_⟩
  have e : (subImg b X').relIndex (subImg b Y) = X'.relIndex Y := by
    unfold subImg
    rw [Subgroup.relIndex_map_map_of_injective _ _ hb]
    unfold Subgroup.subgroupOf
    rw [Subgroup.relIndex_comap]
    rw [Subgroup.map_comap_eq_self (by simpa using hY)]
  have := h.2.2
  show ¬ 2 ∣ (subImg b X').relIndex (subImg b Y)
  rw [e]; exact this

end Img2

section MainOut

variable {X G : Type} [Group X] [Group G] {N₁ N₂ : Subgroup X} {M₁ M₂ : Subgroup G}

theorem L3OutDatum.nonempty_transport (O : L3OutDatum N₁ N₂) (T : AmalgIso N₁ N₂ M₁ M₂) :
    Nonempty (L3OutDatum M₁ M₂) := by
  have hSH : O.S ≤ N₁ ⊓ N₂ := O.S_le_H
  have hS1 : O.S ≤ N₁ := hSH.trans inf_le_left
  have hT1 : O.T ≤ N₁ := O.T_le.trans inf_le_left
  have hB1 : O.B ≤ N₁ := O.B_le.trans inf_le_left
  have hf1 : O.f ∈ N₁ := hT1 O.f_mem
  have hb := T.inj₁
  have hcS : centerOf (subImg T.b₁ O.S) = subImg T.b₁ (centerOf O.S) := subImg_centerOf hb hS1
  have e1 : M₁ ⊓ M₂ = subImg T.b₁ (N₁ ⊓ N₂) := by
    ext x
    rw [T.mem_H, mem_subImg]
    constructor
    · rintro ⟨g, h1, h2, rfl⟩; exact ⟨g, h1, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨g, h1, ⟨h1', h2⟩, rfl⟩; exact ⟨g, h1, h2, rfl⟩
  have hTf : subImg T.b₁ O.T ⊓ Subgroup.centralizer ({T.b₁ ⟨O.f, hf1⟩} : Set G) =
      subImg T.b₁ (O.T ⊓ Subgroup.centralizer ({O.f} : Set X)) :=
    (subImg_inf_centralizer T.b₁ hb hf1 O.T).symm
  have hMf : M₁ ⊓ M₂ ⊓ Subgroup.centralizer ({T.b₁ ⟨O.f, hf1⟩} : Set G) =
      subImg T.b₁ (N₁ ⊓ N₂ ⊓ Subgroup.centralizer ({O.f} : Set X)) := by
    rw [e1]; exact (subImg_inf_centralizer T.b₁ hb hf1 (N₁ ⊓ N₂)).symm
  have hTfN : O.T ⊓ Subgroup.centralizer ({O.f} : Set X) ≤ N₁ := inf_le_left.trans hT1
  have hZ1' : centerOf O.S ≤ N₁ := inf_le_left.trans hS1
  have hZfeq : centerOf (subImg T.b₁ O.T ⊓ Subgroup.centralizer ({T.b₁ ⟨O.f, hf1⟩} : Set G)) ⊓
      ⁅subImg T.b₁ O.T ⊓ Subgroup.centralizer ({T.b₁ ⟨O.f, hf1⟩} : Set G),
        subImg T.b₁ O.T ⊓ Subgroup.centralizer ({T.b₁ ⟨O.f, hf1⟩} : Set G)⁆ =
      subImg T.b₁ (centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set X)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set X),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set X)⁆) := by
    rw [hTf, subImg_centerOf hb hTfN, ← subImg_commutator T.b₁ hTfN, ← subImg_inf' T.b₁ hb]
  refine ⟨
    { S := subImg T.b₁ O.S
      T := subImg T.b₁ O.T
      B := subImg T.b₁ O.B
      f := T.b₁ ⟨O.f, hf1⟩
      S_eq := ?_
      S_le_T := subImg_mono _ O.S_le_T
      T_le := ?_
      T_pgroup := isPGroup_subImg T.b₁ hb hT1 O.T_pgroup
      T_index := ?_
      B_le := ?_
      trans := ?_
      cent := ?_
      ZT := ?_
      invS := ?_
      f_mem := mem_subImg_of_mem _ hf1 O.f_mem
      f_not := ?_
      f_sq := ?_
      T_comm := ?_
      T_cyc := ?_
      Tf_sylow := ?_
      Zf_ne := ?_
      Zf_le := ?_
      Tf_lt := ?_ }⟩
  ·
    rw [e1, subImg_pCoreOf hb inf_le_left, ← O.S_eq]
  ·
    intro g hg
    obtain ⟨x, hx, hxT, rfl⟩ := mem_subImg.mp hg
    exact T.mem_H.mpr ⟨x, hx, (O.T_le hxT).2, rfl⟩
  ·
    have h1 := relIndex_subImg_range T.b₁ hb O.T
    rw [T.range₁] at h1
    rw [h1]; exact O.T_index
  ·
    intro g hg
    obtain ⟨x, hx, hxB, rfl⟩ := mem_subImg.mp hg
    exact T.mem_H.mpr ⟨x, hx, (O.B_le hxB).2, rfl⟩
  ·
    intro x hx hx1 y hy hy1
    rw [hcS] at hx hy
    obtain ⟨x', hx', hxZ, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy', hyZ, rfl⟩ := mem_subImg.mp hy
    have hx1' : x' ≠ 1 := by rintro rfl; exact hx1 (map_one T.b₁)
    have hy1' : y' ≠ 1 := by rintro rfl; exact hy1 (map_one T.b₁)
    obtain ⟨c, hc, hcxy⟩ := O.trans x' hxZ hx1' y' hyZ hy1'
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
    have hy2 : y' ∈ N₂ := O.cent x' hxZ hx1' y' hy' hcomm
    exact T.mem_M₂.mpr ⟨y', hy2, (T.agree y' hy' hy2).symm⟩
  ·
    intro w hw
    rw [subImg_centerOf hb hT1] at hw
    rw [hcS]
    obtain ⟨w', hw', hwZ, rfl⟩ := mem_subImg.mp hw
    exact mem_subImg_of_mem _ hw' (O.ZT w' hwZ)
  ·
    intro x hx hx2 hx1
    obtain ⟨x', hx', hxS, rfl⟩ := mem_subImg.mp hx
    have hx2' : x' * x' = 1 := by
      have h := (sq_eq_one_iff_of_injective hb hx').mp (by rw [pow_two]; exact hx2)
      rwa [pow_two] at h
    have hx1' : x' ≠ 1 := by rintro rfl; exact hx1 (map_one T.b₁)
    obtain ⟨m, hm, hmZ⟩ := O.invS x' hxS hx2' hx1'
    rcases hm with hm | hm
    · refine ⟨T.b₁ ⟨m, hm⟩, Or.inl (T.mem_M₁.mpr ⟨m, hm, rfl⟩), ?_⟩
      rw [hcS]
      have hq : m * x' * m⁻¹ ∈ N₁ := hZ1' hmZ
      have e : T.b₁ ⟨m, hm⟩ * T.b₁ ⟨x', hx'⟩ * (T.b₁ ⟨m, hm⟩)⁻¹ =
          T.b₁ ⟨m * x' * m⁻¹, N₁.mul_mem (N₁.mul_mem hm hx') (N₁.inv_mem hm)⟩ := by
        rw [← map_inv, ← map_mul, ← map_mul]; rfl
      rw [e]; exact mem_subImg_of_mem _ _ hmZ
    · have hx2n : x' ∈ N₂ := (hSH hxS).2
      have hq1 : m * x' * m⁻¹ ∈ N₁ := hZ1' hmZ
      have hq2 : m * x' * m⁻¹ ∈ N₂ := N₂.mul_mem (N₂.mul_mem hm hx2n) (N₂.inv_mem hm)
      refine ⟨T.b₂ ⟨m, hm⟩, Or.inr (T.mem_M₂.mpr ⟨m, hm, rfl⟩), ?_⟩
      rw [hcS]
      have e : T.b₂ ⟨m, hm⟩ * T.b₁ ⟨x', hx'⟩ * (T.b₂ ⟨m, hm⟩)⁻¹ =
          T.b₁ ⟨m * x' * m⁻¹, hq1⟩ := by
        rw [T.agree x' hx' hx2n, T.agree _ hq1 hq2, ← map_inv, ← map_mul, ← map_mul]; rfl
      rw [e]; exact mem_subImg_of_mem _ _ hmZ
  ·
    intro h
    exact O.f_not ((mem_subImg_apply T.b₁ hb hf1).mp h)
  ·
    rw [← map_mul]
    have : (⟨O.f, hf1⟩ * ⟨O.f, hf1⟩ : ↥N₁) = 1 := Subtype.ext O.f_sq
    rw [this, map_one]
  ·
    intro x hx y hy
    obtain ⟨x', hx', hxT, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy', hyT, rfl⟩ := mem_subImg.mp hy
    have e : T.b₁ ⟨x', hx'⟩ * T.b₁ ⟨y', hy'⟩ * (T.b₁ ⟨x', hx'⟩)⁻¹ * (T.b₁ ⟨y', hy'⟩)⁻¹ =
        T.b₁ ⟨x' * y' * x'⁻¹ * y'⁻¹,
          N₁.mul_mem (N₁.mul_mem (N₁.mul_mem hx' hy') (N₁.inv_mem hx')) (N₁.inv_mem hy')⟩ := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]; rfl
    rw [e]; exact mem_subImg_of_mem _ _ (O.T_comm x' hxT y' hyT)
  ·
    intro x hx y hy hxS hyS hx2 hy2
    obtain ⟨x', hx', hxT, rfl⟩ := mem_subImg.mp hx
    obtain ⟨y', hy', hyT, rfl⟩ := mem_subImg.mp hy
    have hxS' : x' ∉ O.S := fun h => hxS (mem_subImg_of_mem _ hx' h)
    have hyS' : y' ∉ O.S := fun h => hyS (mem_subImg_of_mem _ hy' h)
    have ex : T.b₁ ⟨x', hx'⟩ * T.b₁ ⟨x', hx'⟩ = T.b₁ ⟨x' * x', N₁.mul_mem hx' hx'⟩ := by
      rw [← map_mul]; rfl
    have ey : T.b₁ ⟨y', hy'⟩ * T.b₁ ⟨y', hy'⟩ = T.b₁ ⟨y' * y', N₁.mul_mem hy' hy'⟩ := by
      rw [← map_mul]; rfl
    rw [ex] at hx2
    rw [ey] at hy2
    have hx2' : x' * x' ∈ O.S := (mem_subImg_apply T.b₁ hb _).mp hx2
    have hy2' : y' * y' ∈ O.S := (mem_subImg_apply T.b₁ hb _).mp hy2
    have h := O.T_cyc x' hxT y' hyT hxS' hyS' hx2' hy2'
    have e : (T.b₁ ⟨x', hx'⟩)⁻¹ * T.b₁ ⟨y', hy'⟩ =
        T.b₁ ⟨x'⁻¹ * y', N₁.mul_mem (N₁.inv_mem hx') hy'⟩ := by
      rw [← map_inv, ← map_mul]; rfl
    rw [e]; exact mem_subImg_of_mem _ _ h
  ·
    rw [hTf, hMf]
    exact isSylowTwoOf_subImg T.b₁ hb (inf_le_left.trans inf_le_left) O.Tf_sylow
  ·
    rw [hZfeq]
    intro h
    apply O.Zf_ne
    have hZN : centerOf (O.T ⊓ Subgroup.centralizer ({O.f} : Set X)) ⊓
        ⁅O.T ⊓ Subgroup.centralizer ({O.f} : Set X),
          O.T ⊓ Subgroup.centralizer ({O.f} : Set X)⁆ ≤ N₁ :=
      inf_le_left.trans (inf_le_left.trans hTfN)
    exact subImg_injective T.b₁ hb hZN bot_le (h.trans (subImg_bot T.b₁).symm)
  ·
    rw [hZfeq, hcS]
    exact subImg_mono _ O.Zf_le
  ·
    rw [hTf, card_subImg T.b₁ hb hTfN, card_subImg T.b₁ hb hS1]
    exact O.Tf_lt

end MainOut


end CFSG.Quasithin.H13.F431.L3
