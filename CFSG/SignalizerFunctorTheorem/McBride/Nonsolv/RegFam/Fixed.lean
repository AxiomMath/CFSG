module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.FixedAux
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.GenPi

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G]

namespace IsRegFam

variable {A H N : Subgroup G} {Ω : Set (Subgroup G)}

theorem smear_family [Finite G] (hΩ : IsRegFam A H Ω N) (hA : IsMulCommutative A)
    {F : Subgroup G} (hFA : F ≤ A) (hFN : F ⊓ N = ⊥) :
    IsRegFam A (H ⊓ Subgroup.centralizer (F : Set G)) {Y | ∃ L ∈ Ω, Y = smear L F} (N ⊔ F) := by
  have := hA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hFperm : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω :=
    fun f hf J hJ => hΩ.map_conj_mem f (hFA hf) J hJ
  have hfree : ∀ f ∈ F, f ≠ 1 → ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ≠ J := by
    intro f hf hf1 J hJ
    refine hΩ.map_conj_ne (hFA hf) (fun hfN => hf1 ?_) hJ
    have h : f ∈ F ⊓ N := Subgroup.mem_inf.mpr ⟨hf, hfN⟩
    rw [hFN] at h
    exact Subgroup.mem_bot.mp h
  have hconj : ∀ a ∈ A, ∀ L : Subgroup G, (smear L F).map (MulAut.conj a).toMonoidHom =
      smear (L.map (MulAut.conj a).toMonoidHom) F := fun a ha L =>
    Near.Lemma212.smear_map_conj_of_commute L F fun b hb => hcomm b (hFA hb) a ha
  have hne : ∀ L ∈ Ω, smear L F ≠ ⊥ := by
    intro L hL hbot
    have hsm : smear L F ≤ H ⊓ Subgroup.centralizer (F : Set G) :=
      le_inf ((smear_le_orbitClosure L F).trans
        (orbitClosure_le fun f hf => hΩ.isDirectProduct.le (hFperm f hf L hL)))
        (smear_le_centralizer L F)
    have h1 := le_projIn_of_smear_le hΩ.isDirectProduct hFperm hfree hsm hL le_rfl le_rfl
    obtain ⟨⟨x, hxL⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hΩ.ne_bot L hL)
    obtain ⟨y, hy, hyx⟩ := (hΩ.isDirectProduct.mem_projIn_iff hL).mp (h1 hxL)
    rw [hbot, Subgroup.mem_bot] at hy
    have hy1 : y = 1 := Subtype.ext hy
    rw [hy1, map_one] at hyx
    exact hx1 (Subtype.ext hyx.symm)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hblocks := RegFam.isDirectProduct_orbitClosure hΩ.isDirectProduct hFperm
    have hE : ∀ U ∈ {U | ∃ L ∈ Ω, U = orbitClosure L F},
        F ≤ Subgroup.normalizer (U : Set G) := by
      rintro U ⟨L, hL, rfl⟩
      exact Near.Lemma212.le_normalizer_orbitClosure L F
    have h := T614.isDirectProduct_inf_centralizer hblocks hE
    have hset : {Y | ∃ U ∈ {U | ∃ L ∈ Ω, U = orbitClosure L F},
          Y = U ⊓ Subgroup.centralizer (F : Set G)} = {Y | ∃ L ∈ Ω, Y = smear L F} := by
      ext Y
      constructor
      · rintro ⟨_, ⟨L, hL, rfl⟩, rfl⟩
        exact ⟨L, hL, rfl⟩
      · rintro ⟨L, hL, rfl⟩
        exact ⟨orbitClosure L F, ⟨L, hL, rfl⟩, rfl⟩
    rw [hset] at h
    exact h
  · obtain ⟨L, hL⟩ := hΩ.nonempty
    exact ⟨smear L F, L, hL, rfl⟩
  · rintro _ ⟨L, hL, rfl⟩
    exact hne L hL
  · rintro a ha _ ⟨L, hL, rfl⟩
    exact ⟨L.map (MulAut.conj a).toMonoidHom, hΩ.map_conj_mem a ha L hL, hconj a ha L⟩
  · rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩
    obtain ⟨a, ha, rfl⟩ := hΩ.transitive L hL L' hL'
    exact ⟨a, ha, (hconj a ha L).symm⟩
  · rintro _ ⟨L, hL, rfl⟩
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · intro a ha
      obtain ⟨haA, haY⟩ := Subgroup.mem_inf.mp ha
      have h1 : (smear L F).map (MulAut.conj a).toMonoidHom = smear L F :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp haY
      rw [hconj a haA L] at h1
      have hmem : L.map (MulAut.conj a).toMonoidHom ∈ RegFam.conjOrbit L F := by
        by_contra hno
        have hL' := hΩ.map_conj_mem a haA L hL
        have hdisj := RegFam.disjoint_orbitClosure hΩ.isDirectProduct hFperm hL hL' hno
        have h2 : Disjoint (smear L F) (smear L F) :=
          hdisj.mono (smear_le_orbitClosure L F)
            (h1 ▸ smear_le_orbitClosure (L.map (MulAut.conj a).toMonoidHom) F)
        exact hne L hL (disjoint_self.mp h2)
      obtain ⟨f, hf, hfa⟩ := hmem
      have hfaN : f⁻¹ * a ∈ N := by
        rw [← hΩ.stabilizer L hL]
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hFA hf)) haA, ?_⟩
        have h2 : L.map (MulAut.conj (f⁻¹ * a)).toMonoidHom = L := by
          rw [← Near.Thm210.map_conj_map_conj, hfa, Near.Thm210.map_conj_map_conj,
            inv_mul_cancel, Near.Thm210.map_conj_one]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
      have : a = f * (f⁻¹ * a) := by group
      rw [this]
      exact mul_mem (Subgroup.mem_sup_right hf) (Subgroup.mem_sup_left hfaN)
    · intro n hn
      have hnA : n ∈ A := hΩ.le_left hn
      have hnL : n ∈ Subgroup.normalizer (L : Set G) := by
        rw [← hΩ.stabilizer L hL] at hn
        exact (Subgroup.mem_inf.mp hn).2
      refine Subgroup.mem_inf.mpr ⟨hnA, ?_⟩
      have h1 : L.map (MulAut.conj n).toMonoidHom = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hnL
      have h2 : (smear L F).map (MulAut.conj n).toMonoidHom = smear L F := by
        rw [hconj n hnA L, h1]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2
    · intro f hf
      refine Subgroup.mem_inf.mpr ⟨hFA hf, ?_⟩
      exact Subgroup.centralizer_le_normalizer _
        (Subgroup.le_centralizer_iff.mp (smear_le_centralizer L F) hf)

theorem inf_centralizer_family [Finite G] (hΩ : IsRegFam A H Ω N) (hA : IsMulCommutative A)
    {E : Subgroup G} (hEA : E ≤ A) (hEN : E ≤ N)
    (hne : ∀ L ∈ Ω, L ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥) :
    IsRegFam A (H ⊓ Subgroup.centralizer (E : Set G))
      {Y | ∃ L ∈ Ω, Y = L ⊓ Subgroup.centralizer (E : Set G)} N := by
  have := hA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hcent : ∀ a ∈ A, (Subgroup.centralizer (E : Set G)).map (MulAut.conj a).toMonoidHom =
      Subgroup.centralizer (E : Set G) := fun a ha =>
    Near.Lemma212.map_conj_centralizer_of_commute E fun b hb => hcomm b (hEA hb) a ha
  have hconj : ∀ a ∈ A, ∀ L : Subgroup G,
      (L ⊓ Subgroup.centralizer (E : Set G)).map (MulAut.conj a).toMonoidHom =
        L.map (MulAut.conj a).toMonoidHom ⊓ Subgroup.centralizer (E : Set G) := by
    intro a ha L
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj a).injective, hcent a ha]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine T614.isDirectProduct_inf_centralizer hΩ.isDirectProduct fun J hJ => ?_
    rw [← hΩ.stabilizer J hJ] at hEN
    exact hEN.trans inf_le_right
  · obtain ⟨L, hL⟩ := hΩ.nonempty
    exact ⟨_, L, hL, rfl⟩
  · rintro _ ⟨L, hL, rfl⟩
    exact hne L hL
  · rintro a ha _ ⟨L, hL, rfl⟩
    exact ⟨L.map (MulAut.conj a).toMonoidHom, hΩ.map_conj_mem a ha L hL, hconj a ha L⟩
  · rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩
    obtain ⟨a, ha, rfl⟩ := hΩ.transitive L hL L' hL'
    exact ⟨a, ha, (hconj a ha L).symm⟩
  · rintro _ ⟨L, hL, rfl⟩
    refine le_antisymm ?_ ?_
    · intro a ha
      obtain ⟨haA, haY⟩ := Subgroup.mem_inf.mp ha
      have h1 : (L ⊓ Subgroup.centralizer (E : Set G)).map (MulAut.conj a).toMonoidHom =
          L ⊓ Subgroup.centralizer (E : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mp haY
      rw [hconj a haA L] at h1
      by_contra haN
      have hLa := hΩ.map_conj_mem a haA L hL
      have hdisj : Disjoint L (L.map (MulAut.conj a).toMonoidHom) :=
        hΩ.isDirectProduct.indep.pairwiseDisjoint hL hLa (hΩ.map_conj_ne haA haN hL).symm
      have h2 : Disjoint (L ⊓ Subgroup.centralizer (E : Set G))
          (L ⊓ Subgroup.centralizer (E : Set G)) :=
        hdisj.mono inf_le_left (h1 ▸ inf_le_left)
      exact hne L hL (disjoint_self.mp h2)
    · intro n hn
      have hnA : n ∈ A := hΩ.le_left hn
      have hnL : n ∈ Subgroup.normalizer (L : Set G) := by
        rw [← hΩ.stabilizer L hL] at hn
        exact (Subgroup.mem_inf.mp hn).2
      refine Subgroup.mem_inf.mpr ⟨hnA, ?_⟩
      have h1 : L.map (MulAut.conj n).toMonoidHom = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hnL
      have h2 : (L ⊓ Subgroup.centralizer (E : Set G)).map (MulAut.conj n).toMonoidHom =
          L ⊓ Subgroup.centralizer (E : Set G) := by
        rw [hconj n hnA L, h1]
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

end IsRegFam

theorem IsWreath.isRegFam [Finite G] {X A L N C : Subgroup G} (hW : IsWreath (X ⊔ A) L A N C)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hcop : Nat.Coprime (Nat.card A) (Nat.card X))
    (hLX : L ≤ X) (hL1 : L ≠ ⊥) :
    IsRegFam A X {Y | ∃ a ∈ A, Y = L.map (MulAut.conj a).toMonoidHom} N := by
  have := hW.isMulCommutative
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hWX : X ⊔ A ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hAX
  set M : Subgroup G := ⨆ g ∈ X ⊔ A, L.map (MulAut.conj g).toMonoidHom with hM
  have hMX : M ≤ X := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hWX hg) l).mp (hLX hl)
  have hWM : X ⊔ A ≤ Subgroup.normalizer (M : Set G) := by
    refine Near.Thm210.le_normalizer_of_conj_mem fun c hc x hx => ?_
    have hle : M ≤ M.comap (MulAut.conj c).toMonoidHom := by
      refine iSup₂_le fun g hg => ?_
      rw [← Subgroup.map_le_iff_le_comap, Near.Thm210.map_conj_map_conj]
      exact le_iSup₂_of_le (c * g) (mul_mem hc hg) le_rfl
    simpa using hle hx
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := le_sup_right.trans hWM
  have hLM : L ≤ M := by
    refine le_trans (Near.Thm210.map_conj_one L).symm.le ?_
    exact le_iSup₂_of_le (1 : G) (one_mem (X ⊔ A)) le_rfl
  have hXA : X ⊓ A = ⊥ := by
    have h1 : Nat.card ↥(X ⊓ A) ∣ Nat.card A := Subgroup.card_dvd_of_le inf_le_right
    have h2 : Nat.card ↥(X ⊓ A) ∣ Nat.card X := Subgroup.card_dvd_of_le inf_le_left
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one, Nat.dvd_one] at h3
    exact Subgroup.eq_bot_of_card_eq _ h3
  have hXM : X ≤ M := by
    intro x hx
    have hxW : x ∈ M ⊔ A := by
      have h1 : x ∈ L ⊔ A := hW.sup_eq ▸ Subgroup.mem_sup_left hx
      exact sup_le_sup_right hLM A h1
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left M A hAM] at hxW
    obtain ⟨m, hm, a, ha, rfl⟩ := hxW
    have haX : a ∈ X ⊓ A :=
      Subgroup.mem_inf.mpr ⟨by simpa using mul_mem (inv_mem (hMX hm)) hx, ha⟩
    rw [hXA, Subgroup.mem_bot] at haX
    rw [haX]
    simpa using hm
  have hMeq : M = X := le_antisymm hMX hXM
  have hdp : IsDirectProduct {K | ∃ g ∈ X ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} M :=
    hW.isDirectProduct
  have hset : {K | ∃ g ∈ X ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} =
      {Y | ∃ a ∈ A, Y = L.map (MulAut.conj a).toMonoidHom} := by
    ext K
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left X A hAX] at hg
      obtain ⟨x, hxX, a, haA, rfl⟩ := hg
      refine ⟨a, haA, ?_⟩
      have hJ : L.map (MulAut.conj a).toMonoidHom ∈
          {K | ∃ g ∈ X ⊔ A, K = L.map (MulAut.conj g).toMonoidHom} :=
        ⟨a, Subgroup.mem_sup_right haA, rfl⟩
      have h1 : (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj x).toMonoidHom =
          L.map (MulAut.conj a).toMonoidHom :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hdp.le_normalizer hJ (hMeq ▸ hxX))
      rw [← h1, Near.Thm210.map_conj_map_conj]
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, Subgroup.mem_sup_right ha, rfl⟩
  have hdp' : IsDirectProduct {Y | ∃ a ∈ A, Y = L.map (MulAut.conj a).toMonoidHom} X := by
    have h := hdp
    rw [hMeq, hset] at h
    exact h
  refine ⟨hdp', ⟨L, 1, one_mem A, (Near.Thm210.map_conj_one L).symm⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ h
    exact hL1 ((Subgroup.map_eq_bot_iff_of_injective L (MulAut.conj a).injective).mp h)
  · rintro a ha _ ⟨b, hb, rfl⟩
    exact ⟨a * b, mul_mem ha hb, Near.Thm210.map_conj_map_conj L b a⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨b * a⁻¹, mul_mem hb (inv_mem ha), ?_⟩
    rw [Near.Thm210.map_conj_map_conj, inv_mul_cancel_right]
  · rintro _ ⟨a, ha, rfl⟩
    rw [hW.N_eq]
    ext b
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    refine and_congr_right fun hb => ?_
    exact Near.Lemma212.mem_normalizer_map_conj_iff_of_commute (hcomm b hb a ha)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
