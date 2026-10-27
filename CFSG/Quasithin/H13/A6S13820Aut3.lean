module

public import CFSG.Quasithin.H13.A6S13820Aut2
public import CFSG.Quasithin.H13.A6S13820AutBorel

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Aut20

variable {G : Type} [Group G]

noncomputable abbrev mk20 (K : Subgroup G) : ↥K →* ModO2 K :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥K)

theorem subgroupOf_le20 {A B K : Subgroup G} (h : A ≤ B) : A.subgroupOf K ≤ B.subgroupOf K :=
  fun _ hx => Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hx))

theorem mem_map_mk20 {K Y : Subgroup G} (hY : pCoreOf 2 K ≤ Y) (k : ↥K) :
    mk20 K k ∈ (Y.subgroupOf K).map (mk20 K) ↔ (k : G) ∈ Y := by
  constructor
  · rintro ⟨y, hy, hyk⟩
    have h := (QuotientGroup.eq (s := CFSG.pCore 2 ↥K)).1 hyk
    rw [← Setting4.pCoreOf_subgroupOf_eq K] at h
    have h' : (y : G)⁻¹ * k ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp h
    have e : (k : G) = y * ((y : G)⁻¹ * k) := by group
    rw [e]
    exact Y.mul_mem (Subgroup.mem_subgroupOf.mp hy) (hY h')
  · intro hk
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩

theorem mem_normalizer_mk20 [Finite G] {K T : Subgroup G} (hO : pCoreOf 2 K ≤ T ⊓ K) (k : ↥K) :
    mk20 K k ∈ Subgroup.normalizer
        ((((T ⊓ K).subgroupOf K).map (mk20 K) : Subgroup (ModO2 K)) : Set (ModO2 K)) ↔
      (k : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  have hiff : ∀ y : ↥K, ((y : G) ∈ T ⊓ K ↔ (k : G) * y * (k : G)⁻¹ ∈ T ⊓ K) →
      (mk20 K y ∈ ((T ⊓ K).subgroupOf K).map (mk20 K) ↔
        mk20 K k * mk20 K y * (mk20 K k)⁻¹ ∈ ((T ⊓ K).subgroupOf K).map (mk20 K)) := by
    intro y hy
    rw [← map_inv, ← map_mul, ← map_mul, mem_map_mk20 hO, mem_map_mk20 hO]
    exact hy
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff] at h ⊢
    intro x
    constructor
    · intro hx
      have hxK : x ∈ K := hx.2
      have := (h (mk20 K ⟨x, hxK⟩)).1 ((mem_map_mk20 hO _).2 hx)
      rw [← map_inv, ← map_mul, ← map_mul, mem_map_mk20 hO] at this
      exact this
    · intro hx
      have hxK : x ∈ K := by
        have h1 : (k : G) * x * (k : G)⁻¹ ∈ K := hx.2
        have := K.mul_mem (K.mul_mem (K.inv_mem k.2) h1) k.2
        simpa [mul_assoc] using this
      have hmem : mk20 K k * mk20 K ⟨x, hxK⟩ * (mk20 K k)⁻¹ ∈
          ((T ⊓ K).subgroupOf K).map (mk20 K) := by
        rw [← map_inv, ← map_mul, ← map_mul, mem_map_mk20 hO]
        exact hx
      exact (mem_map_mk20 hO _).1 ((h _).2 hmem)
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    induction x using QuotientGroup.induction_on with
    | H y => exact hiff y ((Subgroup.mem_normalizer_iff.mp h) y)

theorem act20_of_mem {K : Subgroup G} {u : G} (hu : u ∈ K)
    (huN : u ∈ Subgroup.normalizer (K : Set G)) :
    act20 K ⟨u, huN⟩ = MulAut.conj (mk20 K ⟨u, hu⟩) := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    rw [act20_mk, MulAut.conj_apply]
    rfl

theorem isSylowTwoOf_Sb20 [Finite G] {K T : Subgroup G} (hsyl : IsSylowTwoOf (T ⊓ K) K) :
    IsSylowTwoOf (((T ⊓ K).subgroupOf K).map (mk20 K)) ⊤ := by
  refine A6S20.isSylowTwoOf_map_top (QuotientGroup.mk'_surjective _) ⟨le_top, ?_, ?_⟩
  · exact hsyl.2.1.comap_of_injective K.subtype Subtype.val_injective
  · show ¬ 2 ∣ ((T ⊓ K).subgroupOf K).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hsyl.2.2

theorem map_act20_eq [Finite G] {K T : Subgroup G} (hO : pCoreOf 2 K ≤ T ⊓ K) {g : G}
    (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (hgT : g ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    (((T ⊓ K).subgroupOf K).map (mk20 K)).map (act20 K ⟨g, hgK⟩).toMonoidHom =
      ((T ⊓ K).subgroupOf K).map (mk20 K) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    show act20 K ⟨g, hgK⟩ (y : ModO2 K) ∈ _
    rw [act20_mk]
    exact (mem_map_mk20 hO _).2 ((Subgroup.mem_normalizer_iff.mp hgT y).mp
      (Subgroup.mem_subgroupOf.mp hy))
  · rintro _ ⟨y, hy, rfl⟩
    have hgK' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hgK
    have hgT' : g⁻¹ ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
      Subgroup.inv_mem _ hgT
    set z : ↥K := ⟨g⁻¹ * y * g⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp hgK' y).mp y.2⟩ with hz
    refine ⟨mk20 K z, (mem_map_mk20 hO _).2 ((Subgroup.mem_normalizer_iff.mp hgT' y).mp
      (Subgroup.mem_subgroupOf.mp hy)), ?_⟩
    show act20 K ⟨g, hgK⟩ (z : ModO2 K) = mk20 K y
    rw [act20_mk]
    congr 1
    apply Subtype.ext
    simp [hz, mul_assoc]

end Aut20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem borelAut20 (h1334 : Stmt13_3_4) {H : Subgroup G}
    (hH : H ∈ S.Hz) {K : Subgroup G} (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hB : Aut20.borel20 T K ≤ Subgroup.normalizer (L : Set G)) {t : G} (ht : t ∈ T ⊓ L)
    (htN : t ∈ Subgroup.normalizer (K : Set G)) :
    BorelAut13820 (((T ⊓ K).subgroupOf K).map (Aut20.mk20 K))
      (((Aut20.borelC20 T K V).subgroupOf K).map (Aut20.mk20 K)) (Aut20.act20 K ⟨t, htN⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hCB, hnorm, hidx, hcomm⟩ := S.borel20_facts h1334 hH hKH hKn hB ht
  have hsyl := S.isSylowTwoOf_TK hH hKH hKn
  have hO : pCoreOf 2 K ≤ T ⊓ K := S.pCoreOf_le_TK hH hKH hKn
  have hTKC : T ⊓ K ≤ Aut20.borelC20 T K V := le_sup_right
  have hOC : pCoreOf 2 K ≤ Aut20.borelC20 T K V := hO.trans hTKC
  have hOB : pCoreOf 2 K ≤ Aut20.borel20 T K := hOC.trans hCB
  set f := Aut20.mk20 K with hf
  set Sb := ((T ⊓ K).subgroupOf K).map f with hSb
  set Cb := ((Aut20.borelC20 T K V).subgroupOf K).map f with hCb
  set Nb := Subgroup.normalizer ((Sb : Subgroup (ModO2 K)) : Set (ModO2 K)) with hNb
  have hNbeq : Nb = ((Aut20.borel20 T K).subgroupOf K).map f := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H k =>
      show f k ∈ Nb ↔ f k ∈ ((Aut20.borel20 T K).subgroupOf K).map f
      rw [hNb, hSb, hf, Aut20.mem_normalizer_mk20 hO, Aut20.mem_map_mk20 hOB]
      exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have hker : f.ker = CFSG.pCore 2 ↥K := QuotientGroup.ker_mk' _
  have hkerC : f.ker ≤ (Aut20.borelC20 T K V).subgroupOf K := by
    rw [hker, ← Setting4.pCoreOf_subgroupOf_eq K]
    exact Aut20.subgroupOf_le20 hOC
  have hkerB : f.ker ≤ (Aut20.borel20 T K).subgroupOf K := hkerC.trans (Aut20.subgroupOf_le20 hCB)
  have hCbNb : Cb ≤ Nb := by
    rw [hNbeq]
    exact Subgroup.map_mono (Aut20.subgroupOf_le20 hCB)
  obtain ⟨kt, hkt⟩ :=
    (isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow le_top).2.1 ⟨t, ht.1⟩
  refine ⟨?_, Subgroup.map_mono (Aut20.subgroupOf_le20 hTKC), hCbNb, ?_, ?_, ⟨kt, ?_⟩, ?_, ?_⟩
  ·
    refine A6S20.isSylowTwoOf_map_top (QuotientGroup.mk'_surjective _) ⟨le_top, ?_, ?_⟩
    · exact hsyl.2.1.comap_of_injective K.subtype Subtype.val_injective
    · show ¬ 2 ∣ ((T ⊓ K).subgroupOf K).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact hsyl.2.2
  ·
    refine ⟨fun c hc n => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    have hn : (n : ModO2 K) ∈ ((Aut20.borel20 T K).subgroupOf K).map f := hNbeq ▸ n.2
    obtain ⟨b, hb, hbn⟩ := hn
    obtain ⟨c', hc', hc'e⟩ := hc
    have e : ((n * c * n⁻¹ : ↥Nb) : ModO2 K) = f (b * c' * b⁻¹) := by
      rw [map_mul, map_mul, map_inv, hbn, hc'e]
      rfl
    rw [e]
    refine ⟨b * c' * b⁻¹, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr (hnorm _ (Subgroup.mem_subgroupOf.mp hb) _
      (Subgroup.mem_subgroupOf.mp hc'))
  ·
    change Cb.relIndex Nb ∣ 3
    rw [hNbeq, hCb, Subgroup.relIndex_map_map, sup_of_le_left hkerC, sup_of_le_left hkerB,
      Subgroup.relIndex_subgroupOf (show Aut20.borel20 T K ≤ K from inf_le_left)]
    exact hidx
  ·
    rw [← map_pow]
    have : (⟨t, htN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ kt = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hkt)
    rw [this, map_one]
  ·
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      induction x using QuotientGroup.induction_on with
      | H y =>
        obtain ⟨y', hy', hy'e⟩ := hx
        rw [← hy'e]
        show Aut20.act20 K ⟨t, htN⟩ (y' : ModO2 K) ∈ Sb
        rw [Aut20.act20_mk]
        refine (Aut20.mem_map_mk20 hO _).2 ?_
        have hy'TK : (y' : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hy'
        exact ⟨T.mul_mem (T.mul_mem ht.1 hy'TK.1) (T.inv_mem ht.1),
          (Subgroup.mem_normalizer_iff.mp htN y').mp y'.2⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have htN' : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ htN
      have hyTK : (y : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hy
      set z : ↥K := ⟨t⁻¹ * y * t⁻¹⁻¹, (Subgroup.mem_normalizer_iff.mp htN' y).mp y.2⟩ with hz
      refine ⟨f z, (Aut20.mem_map_mk20 hO _).2 ⟨?_, z.2⟩, ?_⟩
      · exact T.mul_mem (T.mul_mem (T.inv_mem ht.1) hyTK.1) (by simpa using ht.1)
      · show Aut20.act20 K ⟨t, htN⟩ (z : ModO2 K) = f y
        rw [Aut20.act20_mk]
        congr 1
        apply Subtype.ext
        simp [hz, mul_assoc]
  ·
    rintro _ ⟨c, hc, rfl⟩
    show (f c)⁻¹ * Aut20.act20 K ⟨t, htN⟩ (c : ModO2 K) ∈ Sb
    rw [Aut20.act20_mk, ← map_inv]
    show f (c⁻¹ * _) ∈ Sb
    refine (Aut20.mem_map_mk20 hO _).2 ?_
    exact hcomm _ (Subgroup.mem_subgroupOf.mp hc)

end Setting4

end CFSG.Quasithin.H13.A6
