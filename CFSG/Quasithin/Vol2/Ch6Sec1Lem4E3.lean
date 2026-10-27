module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4E2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4AI

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_iSup₂_ch614 {ι : Type*} {p : ι → Prop} {A : Subgroup G}
    {B : ι → Subgroup G} (h : ∀ i, p i → A ≤ Subgroup.normalizer (B i : Set G)) :
    A ≤ Subgroup.normalizer ((⨆ i, ⨆ (_ : p i), B i : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
  refine iSup_congr fun i => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hi => Subgroup.mem_normalizer_iff_map_conj_eq.mp (h i hi ha)

omit [Finite G] in
theorem le_normalizer_sup_ch614 {A B C : Subgroup G} (hB : A ≤ Subgroup.normalizer (B : Set G))
    (hC : A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB ha),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hC ha)]

omit [Finite G] in
theorem le_normalizer_map_conj_ch614 {A X : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (X : Set G)) (hX : X ≤ Subgroup.normalizer (A : Set G)) :
    X ≤ Subgroup.normalizer ((A.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  intro x hx
  have hx' : t⁻¹ * x * t ∈ X := by
    simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem ht) x).mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_map_conj_ch614, mem_map_conj_ch614]
  have e : t⁻¹ * (x * y * x⁻¹) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) * (t⁻¹ * x * t)⁻¹ := by
    group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp (hX hx') _

omit [Finite G] in
theorem conjClosure_eq_iSup_ch614 (K T : Subgroup G) :
    conjClosure K T = ⨆ t ∈ T, K.map (MulAut.conj t).toMonoidHom := by
  apply le_antisymm
  · exact conjClosure_le fun t ht k hk =>
      (le_biSup (fun t => K.map (MulAut.conj t).toMonoidHom) ht) (conj_mem_map_conj_ch614 hk)
  · refine iSup₂_le fun t ht x hx => ?_
    rw [mem_map_conj_ch614] at hx
    simpa [mul_assoc] using mem_conjClosure ht hx

omit [Finite G] in
theorem inf_mem_normalizer_ch614 {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨(hA x).mp h.1, (hB x).mp h.2⟩, fun h => ⟨(hA x).mpr h.1, (hB x).mpr h.2⟩⟩

theorem eq_sup_inf_of_isSylowTwoOf_ch614 {N₁ N₂ S : Subgroup G}
    (h₁ : N₂ ≤ Subgroup.normalizer (N₁ : Set G)) (h₂ : N₁ ≤ Subgroup.normalizer (N₂ : Set G))
    (hS : IsSylowTwoOf S (N₁ ⊔ N₂)) : S = (S ⊓ N₁) ⊔ (S ⊓ N₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN₁ : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₁ : Set G) := sup_le Subgroup.le_normalizer h₁
  have hN₂ : N₁ ⊔ N₂ ≤ Subgroup.normalizer (N₂ : Set G) := sup_le h₂ Subgroup.le_normalizer
  have hN₁₂ : N₁ ⊔ N₂ ≤ Subgroup.normalizer ((N₁ ⊓ N₂ : Subgroup G) : Set G) := by
    intro y hy
    exact inf_mem_normalizer_ch614 (hN₁ hy) (hN₂ hy)
  have hS₁ := A4.isSylowTwoOf_inf_normal hS le_sup_left hN₁
  have hS₂ := A4.isSylowTwoOf_inf_normal hS le_sup_right hN₂
  have hS₁₂ := A4.isSylowTwoOf_inf_normal hS (inf_le_left.trans le_sup_left) hN₁₂
  rw [inf_inf_distrib_left] at hS₁₂
  set S₁ := S ⊓ N₁ with hS₁def
  set S₂ := S ⊓ N₂ with hS₂def
  have hWS : S₁ ⊔ S₂ ≤ S := sup_le inf_le_left inf_le_left
  have hWY : S₁ ⊔ S₂ ≤ N₁ ⊔ N₂ := hWS.trans hS.1
  have hS₂S₁ : S₂ ≤ Subgroup.normalizer (S₁ : Set G) := by
    intro s hs
    exact inf_mem_normalizer_ch614 (Subgroup.le_normalizer hs.1) (h₁ hs.2)
  have e1 : S₂.relIndex (S₂ ⊔ S₁) = (S₂ ⊓ S₁).relIndex S₁ := relIndex_sup_eq_inf_ch6 hS₂S₁
  have e2 : N₂.relIndex (N₂ ⊔ N₁) = (N₂ ⊓ N₁).relIndex N₁ := relIndex_sup_eq_inf_ch6 h₁
  rw [sup_comm] at e1 e2
  have e3 : S₂.relIndex (S₁ ⊔ S₂) * (S₁ ⊔ S₂).relIndex (N₁ ⊔ N₂) = S₂.relIndex (N₁ ⊔ N₂) :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hWY
  have e4 : S₂.relIndex N₂ * N₂.relIndex (N₁ ⊔ N₂) = S₂.relIndex (N₁ ⊔ N₂) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have e5 : (S₁ ⊓ S₂).relIndex S₁ * S₁.relIndex N₁ = (S₁ ⊓ S₂).relIndex N₁ :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left inf_le_right
  have e6 : (S₁ ⊓ S₂).relIndex (N₁ ⊓ N₂) * (N₁ ⊓ N₂).relIndex N₁ = (S₁ ⊓ S₂).relIndex N₁ :=
    Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_inf inf_le_right inf_le_right) inf_le_left
  rw [inf_comm S₂ S₁] at e1
  rw [inf_comm N₂ N₁] at e2
  have hA : (S₁ ⊓ S₂).relIndex S₁ ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hodd₁ : ¬ 2 ∣ S₁.relIndex N₁ := hS₁.2.2
  have hodd₂ : ¬ 2 ∣ S₂.relIndex N₂ := hS₂.2.2
  have hodd₃ : ¬ 2 ∣ (S₁ ⊓ S₂).relIndex (N₁ ⊓ N₂) := hS₁₂.2.2
  have hW : ¬ 2 ∣ (S₁ ⊔ S₂).relIndex (N₁ ⊔ N₂) := by
    intro hd
    have key : (S₁ ⊓ S₂).relIndex S₁ *
        ((S₁ ⊔ S₂).relIndex (N₁ ⊔ N₂) * (S₁ ⊓ S₂).relIndex (N₁ ⊓ N₂)) =
        (S₁ ⊓ S₂).relIndex S₁ * (S₂.relIndex N₂ * S₁.relIndex N₁) := by
      have h1 : (S₁ ⊓ S₂).relIndex S₁ * (S₁ ⊔ S₂).relIndex (N₁ ⊔ N₂) =
          S₂.relIndex N₂ * (N₁ ⊓ N₂).relIndex N₁ := by rw [← e1, e3, ← e4, e2]
      have h2 : (S₁ ⊓ S₂).relIndex S₁ * S₁.relIndex N₁ =
          (S₁ ⊓ S₂).relIndex (N₁ ⊓ N₂) * (N₁ ⊓ N₂).relIndex N₁ := by rw [e5, e6]
      calc (S₁ ⊓ S₂).relIndex S₁ *
            ((S₁ ⊔ S₂).relIndex (N₁ ⊔ N₂) * (S₁ ⊓ S₂).relIndex (N₁ ⊓ N₂))
          = ((S₁ ⊓ S₂).relIndex S₁ * (S₁ ⊔ S₂).relIndex (N₁ ⊔ N₂)) *
              (S₁ ⊓ S₂).relIndex (N₁ ⊓ N₂) := by ring
        _ = S₂.relIndex N₂ * ((S₁ ⊓ S₂).relIndex (N₁ ⊓ N₂) * (N₁ ⊓ N₂).relIndex N₁) := by
              rw [h1]; ring
        _ = S₂.relIndex N₂ * ((S₁ ⊓ S₂).relIndex S₁ * S₁.relIndex N₁) := by rw [h2]
        _ = (S₁ ⊓ S₂).relIndex S₁ * (S₂.relIndex N₂ * S₁.relIndex N₁) := by ring
    have key' := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hA) key
    have : 2 ∣ S₂.relIndex N₂ * S₁.relIndex N₁ := key' ▸ hd.mul_right _
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h
    · exact hodd₂ h
    · exact hodd₁ h
  have hWSrel : (S₁ ⊔ S₂).relIndex S * S.relIndex (N₁ ⊔ N₂) =
      (S₁ ⊔ S₂).relIndex (N₁ ⊔ N₂) := Subgroup.relIndex_mul_relIndex _ _ _ hWS hS.1
  obtain ⟨n, hn⟩ := IsPGroup.index hS.2.1 ((S₁ ⊔ S₂).subgroupOf S)
  have hn' : (S₁ ⊔ S₂).relIndex S = 2 ^ n := hn
  have hn0 : n = 0 := by
    by_contra hne
    apply hW
    rw [← hWSrel, hn']
    exact (dvd_pow_self 2 hne).mul_right _
  rw [hn0, pow_zero] at hn'
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hn') hWS

theorem inf_iSup_le_ch614 {K T S : Subgroup G}
    (hnorm : ∀ s ∈ T, ∀ t ∈ T, K.map (MulAut.conj s).toMonoidHom ≤
      Subgroup.normalizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hS : IsSylowTwoOf S (conjClosure K T)) (F : Finset G) (hF : (↑F : Set G) ⊆ T) :
    S ⊓ (⨆ t ∈ F, K.map (MulAut.conj t).toMonoidHom) ≤
      ⨆ t ∈ F, S ⊓ K.map (MulAut.conj t).toMonoidHom := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    have haT : a ∈ T := hF (by simp)
    have hFT : (↑F : Set G) ⊆ T := fun x hx => hF (by simp [Finset.mem_coe.mp hx])
    rw [Finset.iSup_insert, Finset.iSup_insert]
    set Ka := K.map (MulAut.conj a).toMonoidHom with hKa
    set YF := ⨆ t ∈ F, K.map (MulAut.conj t).toMonoidHom with hYF
    have h₁ : YF ≤ Subgroup.normalizer (Ka : Set G) :=
      iSup₂_le fun t ht => hnorm t (hFT ht) a haT
    have h₂ : Ka ≤ Subgroup.normalizer (YF : Set G) :=
      le_normalizer_iSup₂_ch614 fun t ht => hnorm a haT t (hFT ht)
    have hK₀ : conjClosure K T = ⨆ t ∈ T, K.map (MulAut.conj t).toMonoidHom :=
      conjClosure_eq_iSup_ch614 K T
    have hKaK₀ : Ka ≤ conjClosure K T := by
      rw [hK₀]; exact le_biSup (fun t => K.map (MulAut.conj t).toMonoidHom) haT
    have hYFK₀ : YF ≤ conjClosure K T := by
      rw [hK₀]
      exact iSup₂_le fun t ht => le_biSup (fun t => K.map (MulAut.conj t).toMonoidHom) (hFT ht)
    have hnormY : conjClosure K T ≤ Subgroup.normalizer ((Ka ⊔ YF : Subgroup G) : Set G) := by
      rw [hK₀]
      refine iSup₂_le fun s hs => le_normalizer_sup_ch614 (hnorm s hs a haT) ?_
      exact le_normalizer_iSup₂_ch614 fun t ht => hnorm s hs t (hFT ht)
    have hS' := A4.isSylowTwoOf_inf_normal hS (sup_le hKaK₀ hYFK₀) hnormY
    have key := eq_sup_inf_of_isSylowTwoOf_ch614 h₁ h₂ hS'
    calc S ⊓ (Ka ⊔ YF) = (S ⊓ (Ka ⊔ YF) ⊓ Ka) ⊔ (S ⊓ (Ka ⊔ YF) ⊓ YF) := key
      _ ≤ (S ⊓ Ka) ⊔ (S ⊓ YF) :=
          sup_le_sup (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ inf_le_left)
      _ ≤ (S ⊓ Ka) ⊔ ⨆ t ∈ F, S ⊓ K.map (MulAut.conj t).toMonoidHom :=
          sup_le_sup_left (ih hFT) _

theorem le_normalizer_inf_conjClosure_ch614 {K T X : Subgroup G}
    (hnorm : ∀ s ∈ T, ∀ t ∈ T, K.map (MulAut.conj s).toMonoidHom ≤
      Subgroup.normalizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hS : IsSylowTwoOf (T ⊓ conjClosure K T) (conjClosure K T))
    (hTX : T ≤ Subgroup.normalizer (X : Set G))
    (hX : X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    X ≤ Subgroup.normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G) := by
  classical
  set F := (Set.toFinite (T : Set G)).toFinset with hF
  have hFT : (↑F : Set G) ⊆ T := fun x hx => by simpa [hF] using hx
  have hsup : (⨆ t ∈ F, K.map (MulAut.conj t).toMonoidHom) = conjClosure K T := by
    rw [conjClosure_eq_iSup_ch614]
    refine iSup_congr fun t => ?_
    simp [hF]
  have hle := inf_iSup_le_ch614 hnorm hS F hFT
  rw [hsup, inf_right_idem] at hle
  have heq : T ⊓ conjClosure K T = ⨆ t ∈ F, T ⊓ conjClosure K T ⊓
      K.map (MulAut.conj t).toMonoidHom :=
    le_antisymm hle (iSup₂_le fun _ _ => inf_le_left)
  rw [heq]
  refine le_normalizer_iSup₂_ch614 fun t ht => ?_
  have htT : t ∈ T := hFT ht
  have hKt : K.map (MulAut.conj t).toMonoidHom ≤ conjClosure K T := by
    rw [conjClosure_eq_iSup_ch614]
    exact le_biSup (fun t => K.map (MulAut.conj t).toMonoidHom) htT
  have e : T ⊓ conjClosure K T ⊓ K.map (MulAut.conj t).toMonoidHom =
      (T ⊓ K).map (MulAut.conj t).toMonoidHom := by
    rw [inf_assoc, inf_eq_right.mpr hKt, Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective,
      show T.map (MulAut.conj t).toMonoidHom = T from
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer htT)]
  rw [e]
  exact le_normalizer_map_conj_ch614 (hTX htT) hX

end CFSG.Quasithin.H13
