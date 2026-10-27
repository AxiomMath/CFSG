module

public import CFSG.Quasithin.Background.F1Hyp
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

universe u

namespace F1

variable {G : Type u} [Group G]

theorem mem_sup_iff_exists_mul_of_le_normalizer {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  constructor
  · intro hx
    let T : Subgroup G :=
      { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, x = a * b}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', H.mul_mem ha ha', a'⁻¹ * b * a' * b', ?_, by group⟩
          refine K.mul_mem ?_ hb'
          have := (Subgroup.mem_normalizer_iff.mp (h (H.inv_mem ha')) b).mp hb
          simpa using this
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, H.inv_mem ha, a * b⁻¹ * a⁻¹, ?_, by group⟩
          have := (Subgroup.mem_normalizer_iff.mp (h ha) b⁻¹).mp (K.inv_mem hb)
          exact this }
    have hle : H ⊔ K ≤ T := sup_le (fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩)
      (fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact (H ⊔ K).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem mem_sup_iff_exists_mul_of_normalizes {H K : Subgroup G}
    (h : K ≤ Subgroup.normalizer (H : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  constructor
  · intro hx
    rw [sup_comm] at hx
    obtain ⟨b, hb, a, ha, rfl⟩ := (mem_sup_iff_exists_mul_of_le_normalizer h).mp hx
    refine ⟨b * a * b⁻¹, ?_, b, hb, by group⟩
    exact (Subgroup.mem_normalizer_iff.mp (h hb) a).mp ha
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact (H ⊔ K).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

theorem conjSub_eq_of_mem_normalizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : conjSub g H = H := by
  ext x
  rw [mem_conjSub]
  have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x
  simpa using this.symm

theorem le_normalizer_sup {X H K : Subgroup G} (hH : X ≤ Subgroup.normalizer (H : Set G))
    (hK : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have e : ∀ g' ∈ X, conjSub g' (H ⊔ K) = H ⊔ K := fun g' hg' => by
    rw [conjSub_sup, conjSub_eq_of_mem_normalizer (hH hg'), conjSub_eq_of_mem_normalizer (hK hg')]
  intro g hg
  exact mem_normalizer_of_conj_le (e g hg).le (e g⁻¹ (X.inv_mem hg)).le

theorem mem_normalizer_normalizer {g : G} {H : Subgroup G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    g ∈ Subgroup.normalizer ((Subgroup.normalizer (H : Set G) : Subgroup G) : Set G) := by
  have e : ∀ g' ∈ Subgroup.normalizer (H : Set G),
      conjSub g' (Subgroup.normalizer (H : Set G)) = Subgroup.normalizer (H : Set G) :=
    fun g' hg' => by rw [← conjSub_normalizer, conjSub_eq_of_mem_normalizer hg']
  exact mem_normalizer_of_conj_le (e g hg).le (e g⁻¹ ((Subgroup.normalizer _).inv_mem hg)).le

theorem sylow_le_borelOf (Li S : Subgroup G) : S ⊓ Li ≤ borelOf Li S :=
  le_inf inf_le_right Subgroup.le_normalizer

theorem borelOf_le (Li S : Subgroup G) : borelOf Li S ≤ Li := inf_le_left

theorem borelOf_le_normalizer (Li S : Subgroup G) :
    borelOf Li S ≤ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) := inf_le_right

theorem le_normalizer_inf_of_le {Li S : Subgroup G} (hS : S ≤ Subgroup.normalizer (Li : Set G)) :
    S ≤ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) :=
  fun _ hs => mem_normalizer_inf (Subgroup.le_normalizer hs) (hS hs)

theorem le_normalizer_borelOf {Li S : Subgroup G} (hS : S ≤ Subgroup.normalizer (Li : Set G)) :
    S ≤ Subgroup.normalizer ((borelOf Li S : Subgroup G) : Set G) :=
  fun _ hs => mem_normalizer_inf (hS hs)
    (mem_normalizer_normalizer (le_normalizer_inf_of_le hS hs))

variable [Finite G]

theorem pCoreOf_borelOf {Li S : Subgroup G} (h : IsSylowTwoOf (S ⊓ Li) Li) :
    pCoreOf 2 (borelOf Li S) = S ⊓ Li := by
  apply le_antisymm
  · exact isSylowTwoOf_pCoreOf_le
      (isSylowTwoOf_mono_right h (sylow_le_borelOf Li S) (borelOf_le Li S))
  · exact le_pCoreOf_of_le_normalizer 2 (sylow_le_borelOf Li S) (borelOf_le_normalizer Li S) h.2.1

theorem exists_isSylowTwoOf_ge {P H : Subgroup G} (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ S : Subgroup G, IsSylowTwoOf S H ∧ P ≤ S := by
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hQS : (Q : Subgroup H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  refine ⟨(Q : Subgroup H).map H.subtype, ⟨hQS, Q.isPGroup'.map H.subtype, ?_⟩, ?_⟩
  · change ¬ 2 ∣ (Subgroup.comap H.subtype ((Q : Subgroup H).map H.subtype)).index
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact Sylow.not_dvd_index Q
  · intro x hx
    have := hQ (show (⟨x, hPH hx⟩ : H) ∈ P.subgroupOf H from hx)
    exact ⟨_, this, rfl⟩

theorem eq_of_isSylowTwoOf_le {T H R : Subgroup G} (h : IsSylowTwoOf T H) (hRH : R ≤ H)
    (hR : IsPGroup 2 R) (hTR : T ≤ R) : T = R := by
  obtain ⟨x, -, hx⟩ := isSylowTwoOf_exists_conj_le h hRH hR
  have h1 : Nat.card R ≤ Nat.card (conjSub x T) := Subgroup.card_le_of_le hx
  have h2 : Nat.card (conjSub x T) = Nat.card T :=
    Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj x))
  exact Subgroup.eq_of_le_of_card_ge hTR (h2 ▸ h1)

omit [Finite G] in
theorem relIndex_sup_eq_of_le_normalizer {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

omit [Finite G] in
theorem mem_pCore_iff_coe {H : Subgroup G} (x : H) : x ∈ pCore 2 H ↔ (x : G) ∈ pCoreOf 2 H :=
  (CFSG.mem_openPCoreOf_iff_open x).symm

end F1

end CFSG.Quasithin
