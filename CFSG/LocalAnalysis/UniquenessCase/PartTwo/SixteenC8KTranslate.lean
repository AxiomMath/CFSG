module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c8k_characteristic_map_equiv {X Y : Type} [Group X] [Group Y]
    {H : Subgroup X} (hH : H.Characteristic) (e : X ≃* Y) :
    (H.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq] at hH ⊢
  intro ψ
  have hcomp : ψ.toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp ((e.trans ψ).trans e.symm).toMonoidHom := by
    ext x
    simp
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  exact congrArg (fun K : Subgroup X => K.map e.toMonoidHom) (hH ((e.trans ψ).trans e.symm))

theorem c8k_sylow_top {M K S U : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S K)
    (hSM : S ≤ M) (hU : IsSylowIn 2 U (M ⊓ K)) :
    IsSylowIn 2 (U.subgroupOf K) (⊤ : Subgroup ↥K) := by
  have hS' : IsSylowIn 2 S K := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
  have hUK : U ≤ K := hU.le.trans inf_le_right
  have h1 : S.relIndex (M ⊓ K) * (M ⊓ K).relIndex K = S.relIndex K :=
    Subgroup.relIndex_mul_relIndex S (M ⊓ K) K (le_inf hSM hS'.le) inf_le_right
  have h2 : ¬ 2 ∣ (M ⊓ K).relIndex K :=
    fun h => hS'.not_dvd_relIndex (h.trans ⟨S.relIndex (M ⊓ K), by rw [mul_comm, ← h1]⟩)
  have h3 : U.relIndex (M ⊓ K) * (M ⊓ K).relIndex K = U.relIndex K :=
    Subgroup.relIndex_mul_relIndex U (M ⊓ K) K hU.le inf_le_right
  have h4 : ¬ 2 ∣ U.relIndex K := by
    rw [← h3]
    rintro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h' | h'
    · exact hU.not_dvd_relIndex h'
    · exact h2 h'
  refine ⟨le_top, hU.isPGroup.comap_subtype, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact h4

theorem c8k_q_le_of_sylow {M K S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S K)
    (hSM : S ≤ M) : CFSG.pCore 2 ↥K ≤ (K ⊓ M).subgroupOf K := by
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have h1 : CFSG.pCore 2 ↥K ≤ (Q : Subgroup ↥K) :=
    IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup Q
  rw [hQ] at h1
  intro x hx
  exact ⟨x.2, hSM (h1 hx)⟩

theorem c8_invthree_of_k {K : Subgroup G}
    (h : ∀ t : ↥K, t ^ 2 = 1 → t ∈ CFSG.pPrimeCore 3 ↥K) :
    ∃ N : Subgroup G, N ≤ K ∧ (N.subgroupOf K).Normal ∧ ¬ 3 ∣ Nat.card N ∧
      ∀ t ∈ K, t ^ 2 = 1 → t ∈ N := by
  let P : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let N : Subgroup G := P.map K.subtype
  have hNK : N ≤ K := Subgroup.map_subtype_le P
  have hsub : N.subgroupOf K = P :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective P
  have hnorm : (N.subgroupOf K).Normal := by
    rw [hsub]
    infer_instance
  have hcard : Nat.card N = Nat.card P :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hcop : Nat.Coprime 3 (Nat.card P) :=
    CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K)
  have hnd : ¬ 3 ∣ Nat.card N := by
    rw [hcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
  refine ⟨N, hNK, hnorm, hnd, ?_⟩
  intro t ht hsq
  exact Subgroup.mem_map.2
    ⟨⟨t, ht⟩, h ⟨t, ht⟩ (Subtype.ext (by simpa using hsq)), rfl⟩

theorem c8_transport_char {K T' : Subgroup G} {C : Subgroup ↥K} (hC1 : C ≠ ⊥)
    (hCS : C ≤ (T' ⊓ K).subgroupOf K)
    (hchar : (C.subgroupOf ((T' ⊓ K).subgroupOf K)).Characteristic) (hn : C.Normal) :
    ∃ C' : Subgroup G, C' ≠ ⊥ ∧ C' ≤ T' ⊓ K ∧ (C'.subgroupOf (T' ⊓ K)).Characteristic ∧
      (C'.subgroupOf K).Normal := by
  let S : Subgroup ↥K := (T' ⊓ K).subgroupOf K
  let C' : Subgroup G := C.map K.subtype
  refine ⟨C', ?_, ?_, ?_, ?_⟩
  · intro hbot
    exact hC1 ((Subgroup.map_eq_bot_iff_of_injective C K.subtype_injective).1 hbot)
  · rintro x ⟨y, hy, rfl⟩
    exact hCS hy
  · have hmap : (C.subgroupOf S).map
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : T' ⊓ K ≤ K)).toMonoidHom =
        C'.subgroupOf (T' ⊓ K) := by
      let e : ↥S ≃* ↥(T' ⊓ K) := Subgroup.subgroupOfEquivOfLe inf_le_right
      change (C.subgroupOf S).map e.toMonoidHom = C'.subgroupOf (T' ⊓ K)
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact Subgroup.mem_map.2 ⟨(y : ↥K), hy, rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ :=
          Subgroup.mem_map.1 (show (x : G) ∈ C.map K.subtype from hx)
        refine Subgroup.mem_map.2 ⟨⟨y, hCS hy⟩, hy, ?_⟩
        exact Subtype.ext hyx
    rw [← hmap]
    exact c8k_characteristic_map_equiv hchar
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : T' ⊓ K ≤ K))
  · have hsub : C'.subgroupOf K = C :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective C
    rw [hsub]
    exact hn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
