module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecBase
public import CFSG.Quasithin.EmptyFaithful.S152FinShape

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open Equiv

variable {G : Type} [Group G] {H L N U : Subgroup G}
  (hs : IsSec H L N) {n : ℕ} (θ : ↥H →* Perm (Fin n)) (hθ : Function.Surjective θ)
  (hk : θ.ker ≤ (cSecIn H L N).subgroupOf H)

@[expose] def secPreimage (V : Subgroup hs.W) : Subgroup G :=
  (V.comap hs.proj).map N.subtype

theorem mem_secPreimage {V : Subgroup hs.W} {y : G} :
    y ∈ secPreimage hs V ↔ ∃ x : ↥N, hs.proj x ∈ V ∧ (x : G) = y := by
  simp only [secPreimage, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]

@[expose] def secImage (K : Subgroup G) : Subgroup hs.W :=
  (K.subgroupOf N).map hs.proj

theorem mem_secImage {K : Subgroup G} {w : hs.W} :
    w ∈ secImage hs K ↔ ∃ x : ↥N, (x : G) ∈ K ∧ hs.proj x = w := by
  simp only [secImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem exists_toPerm_of_quot {H : Subgroup G} {n : ℕ} (hq : Nonempty (OTwoQuot H ≃* Perm (Fin n))) :
    ∃ φ : ↥H →* Perm (Fin n), Function.Surjective φ ∧
      ∀ x : ↥H, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  obtain ⟨ι⟩ := hq
  refine ⟨ι.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)),
    ι.surjective.comp (QuotientGroup.mk'_surjective _), fun x => ?_⟩
  have h1 : (x ∈ CFSG.Open.pCore 2 ↥H) ↔ (x : G) ∈ pCoreOf 2 H := by
    rw [← S152Fin.pCoreOf_subgroupOf H, Subgroup.mem_subgroupOf]
  show ι (QuotientGroup.mk x) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, h1]

section Finite

variable [Finite G]

theorem secModule_isIrred_of_isChiefStep (hstep : IsChiefStep H U L N) :
    (secModule hs θ hθ hk).IsIrred := by
  obtain ⟨hNU, -, hLN, hmin⟩ := hstep
  refine ⟨?_, fun V hV => ?_⟩
  · obtain ⟨x, hxN, hxL⟩ := IsConcreteLE.exists_of_lt hLN
    exact ⟨hs.proj ⟨x, hxN⟩, fun h1 => hxL ((hs.proj_eq_one_iff _).mp h1)⟩
  · have hLK : L ≤ secPreimage hs V := fun l hl =>
      (mem_secPreimage hs).mpr ⟨⟨l, hs.le hl⟩, by
        rw [(hs.proj_eq_one_iff _).mpr hl]; exact V.one_mem, rfl⟩
    have hKN : secPreimage hs V ≤ N := fun y hy => by
      obtain ⟨x, -, rfl⟩ := (mem_secPreimage hs).mp hy
      exact x.2
    have hK : IsNormalIn H U (secPreimage hs V) := by
      refine ⟨hKN.trans hNU.1, fun g hg y hy => ?_⟩
      obtain ⟨x, hxV, rfl⟩ := (mem_secPreimage hs).mp hy
      refine (mem_secPreimage hs).mpr ⟨hs.conjN ⟨g, hg⟩ x, ?_, rfl⟩
      rw [← secModule_act_proj hs θ hθ hk]
      exact hV _ (Subgroup.mem_top _) _ hxV
    rcases hmin _ hK hLK hKN with h | h
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨x, rfl⟩ := hs.proj_surjective w
      have : (x : G) ∈ secPreimage hs V := (mem_secPreimage hs).mpr ⟨x, hw, rfl⟩
      rw [h] at this
      exact (Subgroup.mem_bot.mpr ((hs.proj_eq_one_iff _).mpr this))
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨x, rfl⟩ := hs.proj_surjective w
      have : (x : G) ∈ secPreimage hs V := by rw [h]; exact x.2
      obtain ⟨x', hx', hxx'⟩ := (mem_secPreimage hs).mp this
      rwa [← Subtype.ext hxx']

theorem isChiefStep_of_secModule_isIrred (hN : IsNormalIn H U N) (hL : IsNormalIn H U L)
    (hirr : (secModule hs θ hθ hk).IsIrred) : IsChiefStep H U L N := by
  obtain ⟨⟨w, hw⟩, hirr⟩ := hirr
  have hLN : L < N := by
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    refine lt_of_le_of_ne hs.le fun h => hw ?_
    exact (hs.proj_eq_one_iff x).mpr (h ▸ x.2)
  refine ⟨hN, hL, hLN, fun K hK hLK hKN => ?_⟩
  have hinv : IsInvSub (secModule hs θ hθ hk) ⊤ (secImage hs K) := by
    intro b _ w hw
    obtain ⟨g, rfl⟩ := hθ b
    obtain ⟨x, hxK, rfl⟩ := (mem_secImage hs).mp hw
    refine (mem_secImage hs).mpr ⟨hs.conjN g x, ?_, ?_⟩
    · exact hK.2 g g.2 x hxK
    · exact (secModule_act_proj hs θ hθ hk g x).symm
  rcases hirr _ hinv with h | h
  · left
    refine le_antisymm (fun y hy => ?_) hLK
    have : hs.proj ⟨y, hKN hy⟩ ∈ secImage hs K := (mem_secImage hs).mpr ⟨_, hy, rfl⟩
    have h2 := Subgroup.mem_bot.mp
      (h ▸ this : _ ∈ (⊥ : Subgroup (secModule hs θ hθ hk).W))
    exact (hs.proj_eq_one_iff _).mp h2
  · right
    refine le_antisymm hKN (fun y hy => ?_)
    have : hs.proj ⟨y, hy⟩ ∈ secImage hs K := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨x, hxK, hxy⟩ := (mem_secImage hs).mp this
    have h1 : (x : G)⁻¹ * y ∈ L := (hs.proj_eq_proj_iff x ⟨y, hy⟩).mp hxy
    have e : y = (x : G) * ((x : G)⁻¹ * y) := by group
    rw [e]
    exact K.mul_mem hxK (hLK h1)

theorem secModule_isIrred_iff (hN : IsNormalIn H U N) (hL : IsNormalIn H U L) :
    (secModule hs θ hθ hk).IsIrred ↔ IsChiefStep H U L N :=
  ⟨isChiefStep_of_secModule_isIrred hs θ hθ hk hN hL, secModule_isIrred_of_isChiefStep hs θ hθ hk⟩

theorem natCard_secModule : Nat.card (secModule hs θ hθ hk).W = L.relIndex N := by
  have := hs.normal_subgroupOf
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_card]
  rfl

end Finite

end CFSG.Quasithin.F53Mod
