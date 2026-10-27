module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Off3

public section

namespace CFSG.Quasithin.Fan86.Sigma3

open CFSG.Open CFSG.Quasithin

variable {H : Type*} [Group H] {S : Subgroup H}

theorem thompsonJ_le_self : thompsonJ S ≤ S := iSup₂_le fun _ hA => hA.1

theorem isMax_conj {Q : Subgroup H} (hQ : Q.Normal) (hQS : Q ≤ S) {A : Subgroup H}
    (hA : IsMaxElemAbelian S A) (hAQ : A ≤ Q) (g : H) :
    IsMaxElemAbelian S (A.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩, fun B hB hBe => ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact hQS (hQ.conj_mem a (hAQ ha) g)
  · obtain ⟨a, ha, hau⟩ := u.2
    obtain ⟨b, hb, hbv⟩ := v.2
    apply Subtype.ext
    show u.1 * v.1 = v.1 * u.1
    rw [← hau, ← hbv]
    have hab := elem_comm hA.2.1 ha hb
    calc (MulAut.conj g).toMonoidHom a * (MulAut.conj g).toMonoidHom b
        = (MulAut.conj g).toMonoidHom (a * b) := (map_mul _ _ _).symm
      _ = (MulAut.conj g).toMonoidHom (b * a) := by rw [hab]
      _ = (MulAut.conj g).toMonoidHom b * (MulAut.conj g).toMonoidHom a := map_mul _ _ _
  · obtain ⟨a, ha, rfl⟩ := hy
    rw [← map_pow, hA.2.1.2 a ha, map_one]
  · have := hA.2.2 B hB hBe
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]

variable [Finite H] {x : H}

theorem Hyp3.not_J_le_Q (h : Hyp3 H S x) : ¬ thompsonJ S ≤ oQ H := by
  intro hJQ
  have hQn : (oQ H).Normal := inferInstance
  have hQS := h.sig.Q_le_S
  have hc := CFSG.QuasithinUnique.Setup.characteristic_thompsonJ S
  have hconj : ∀ k ∈ thompsonJ S, x * k * x⁻¹ ∈ thompsonJ S := by
    have hle : thompsonJ S ≤ (thompsonJ S).comap (MulAut.conj x).toMonoidHom := by
      refine iSup₂_le fun A hA => ?_
      have hAQ : A ≤ oQ H :=
        (le_iSup₂ (f := fun A (_ : IsMaxElemAbelian S A) => A) A hA).trans hJQ
      have h2 : A.map (MulAut.conj x).toMonoidHom ≤ thompsonJ S :=
        le_iSup₂ (f := fun A (_ : IsMaxElemAbelian S A) => A) _ (isMax_conj hQn hQS hA hAQ x)
      exact Subgroup.map_le_iff_le_comap.1 h2
    intro k hk
    simpa using hle hk
  have hJnorm : (thompsonJ S).Normal := by
    refine normal_of_gen (mul_mul_eq_one_of_orderOf h.ord) (h.sig.gen h.ord) _ ?_ hconj
    intro s hs k hk
    have := hc
    have hn : ((thompsonJ S).subgroupOf S).Normal := inferInstance
    have := hn.conj_mem ⟨k, thompsonJ_le_self hk⟩ (Subgroup.mem_subgroupOf.2 hk) ⟨s, hs⟩
    exact Subgroup.mem_subgroupOf.1 this
  exact CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot h.sig.two h.sig.S_ne_bot
    (h.no _ thompsonJ_le_self hc hJnorm)

end CFSG.Quasithin.Fan86.Sigma3
