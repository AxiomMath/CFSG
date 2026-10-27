module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.C58

open CFSG.Open CFSG.QuasithinUnique Subgroup

universe u v

variable {X : Type u} [Group X] {G : Type v} [Group G] {f : X →* G}

theorem pCoreOf_map_of_injective (hf : Function.Injective f) (p : ℕ) (L : Subgroup X) :
    pCoreOf p (L.map f) = (pCoreOf p L).map f := by
  set e : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  have h := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  have hc : (L.map f).subtype.comp e.toMonoidHom = f.comp L.subtype := by
    ext x; rfl
  unfold pCoreOf
  rw [← h, Subgroup.map_map, hc, ← Subgroup.map_map]

theorem map_inf_centralizer_of_injective (hf : Function.Injective f) (A B : Subgroup X) :
    (A ⊓ centralizer (B : Set X)).map f = A.map f ⊓ centralizer (B.map f : Set G) := by
  ext y
  constructor
  · rintro ⟨a, ⟨haA, haC⟩, rfl⟩
    refine ⟨⟨a, haA, rfl⟩, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp haC) b hb]
  · rintro ⟨⟨a, haA, rfl⟩, hC⟩
    refine ⟨a, ⟨haA, mem_centralizer_iff.mpr fun b hb => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.mp hC) (f b) ⟨b, hb, rfl⟩

theorem blockQ_map_of_injective (hf : Function.Injective f) (L : Subgroup X) :
    blockQ (L.map f) = (blockQ L).map f :=
  pCoreOf_map_of_injective hf 2 L

theorem blockU_map_of_injective (hf : Function.Injective f) (L : Subgroup X) :
    blockU (L.map f) = (blockU L).map f := by
  unfold blockU
  rw [blockQ_map_of_injective hf, Subgroup.map_commutator]

theorem blockZ_map_of_injective (hf : Function.Injective f) (L : Subgroup X) :
    blockZ (L.map f) = (blockZ L).map f := by
  unfold blockZ
  rw [blockU_map_of_injective hf, map_inf_centralizer_of_injective hf]

theorem card_quotient_pCore_map (hf : Function.Injective f) (L : Subgroup X) :
    Nat.card (↥(L.map f) ⧸ CFSG.pCore 2 ↥(L.map f)) = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  set e : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  have h := CFSG.pCore_map_iso 2 e
  exact (Nat.card_congr (QuotientGroup.congr _ _ e h).toEquiv).symm

theorem isShort2_map_of_injective (hf : Function.Injective f) {L : Subgroup X}
    (hL : IsShort2 L) (h3 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 3) : IsShort2 (L.map f) := by
  obtain ⟨h1, h2, ⟨h3a, h3b⟩, -, h5a, h5b⟩ := hL
  set e : ↥L ≃* ↥(L.map f) := L.equivMapOfInjective f hf
  refine ⟨?_, ?_, ⟨?_, ?_⟩, Or.inr ?_, ?_, ?_⟩
  ·
    intro N _ hN
    set N' : Subgroup L := N.comap e.toMonoidHom
    have hNe : N'.map e.toMonoidHom = N := Subgroup.map_comap_eq_self_of_surjective e.surjective N
    have hN'n : N'.Normal := Subgroup.Normal.comap inferInstance _
    have hN' : IsPGroup 2 (↥L ⧸ N') := hN.of_equiv (QuotientGroup.congr N' N e hNe).symm
    have htop := h1 N' hN'
    rw [← hNe, htop, Subgroup.map_top_of_surjective _ e.surjective]
  ·
    show L.map f ⊓ centralizer (pCoreOf 2 (L.map f) : Set G) ≤ pCoreOf 2 (L.map f)
    rw [pCoreOf_map_of_injective hf, ← map_inf_centralizer_of_injective hf]
    exact Subgroup.map_mono h2
  · rw [blockU_map_of_injective hf, blockQ_map_of_injective hf,
      ← map_inf_centralizer_of_injective hf]
    exact Subgroup.map_mono h3a
  · rw [blockU_map_of_injective hf]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h3b x hx, map_one]
  · rw [card_quotient_pCore_map hf]; exact h3
  · rw [blockZ_map_of_injective hf, blockU_map_of_injective hf]
    exact lt_of_le_of_ne (Subgroup.map_mono h5a.le)
      (fun heq => h5a.ne (Subgroup.map_injective hf heq))
  · intro W hZW hWU hLW
    rw [blockZ_map_of_injective hf] at hZW ⊢
    rw [blockU_map_of_injective hf] at hWU ⊢
    have hWr : W ≤ f.range := hWU.trans (Subgroup.map_le_range f _)
    have hWe : (W.comap f).map f = W := Subgroup.map_comap_eq_self hWr
    have hZW' : blockZ L ≤ W.comap f := fun z hz => hZW ⟨z, hz, rfl⟩
    have hWU' : W.comap f ≤ blockU L := by
      intro w hw
      obtain ⟨u, hu, hu'⟩ := hWU hw
      rwa [hf hu'] at hu
    have hLW' : L ≤ normalizer (W.comap f : Set X) := by
      intro l hl
      have hfl := hLW ⟨l, hl, rfl⟩
      rw [mem_normalizer_iff] at hfl ⊢
      intro w
      have := hfl (f w)
      simp only [Subgroup.mem_comap, map_mul, map_inv] at this ⊢
      exact this
    rcases h5b (W.comap f) hZW' hWU' hLW' with h | h
    · left; rw [← hWe, h]
    · right; rw [← hWe, h]

end CFSG.Quasithin.C58
