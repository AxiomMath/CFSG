module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps139Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

private def w1369_Complemented (P : Subgroup (MulAut W)) : Prop :=
  ∀ B : Subgroup W, StableUnder P B →
    ∃ C : Subgroup W, StableUnder P C ∧ B ⊔ C = ⊤ ∧ B ⊓ C = ⊥

private theorem w1369_stableUnder_sup {P : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder P A) (hB : StableUnder P B) : StableUnder P (A ⊔ B) := by
  intro x hx w hw
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA x hx y hy) (hB x hx z hz)

private theorem w1369_stableUnder_inf {P : Subgroup (MulAut W)} {A B : Subgroup W}
    (hA : StableUnder P A) (hB : StableUnder P B) : StableUnder P (A ⊓ B) := by
  intro x hx w hw
  exact ⟨hA x hx w hw.1, hB x hx w hw.2⟩

private theorem w1369_stableUnder_iSup {ι : Sort*} {P : Subgroup (MulAut W)}
    {U : ι → Subgroup W} (hU : ∀ i, StableUnder P (U i)) : StableUnder P (⨆ i, U i) := by
  intro x hx w hw
  refine Subgroup.iSup_induction U (C := fun y => x y ∈ ⨆ i, U i) hw ?_ ?_ ?_
  · intro i y hy
    exact Subgroup.mem_iSup_of_mem i (hU i x hx y hy)
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro y z hy hz
    rw [map_mul]
    exact Subgroup.mul_mem _ hy hz

private def w1369_MinStable (P : Subgroup (MulAut W)) (S : Subgroup W) : Prop :=
  StableUnder P S ∧ S ≠ ⊥ ∧
    ∀ T : Subgroup W, StableUnder P T → T ≤ S → T = ⊥ ∨ T = S

private noncomputable def w1369_minStableJoin (P : Subgroup (MulAut W)) : Subgroup W :=
  ⨆ (S : {T : Subgroup W // w1369_MinStable P T}), (S : Subgroup W)

private theorem w1369_minStableJoin_stable (P : Subgroup (MulAut W)) :
    StableUnder P (w1369_minStableJoin P) := by
  unfold w1369_minStableJoin
  exact w1369_stableUnder_iSup
    (fun S : {T : Subgroup W // w1369_MinStable P T} => S.2.1)

private theorem w1369_le_minStableJoin {P : Subgroup (MulAut W)} {S : Subgroup W}
    (hS : w1369_MinStable P S) : S ≤ w1369_minStableJoin P := by
  unfold w1369_minStableJoin
  exact le_iSup (fun T : {T : Subgroup W // w1369_MinStable P T} => (T : Subgroup W))
    ⟨S, hS⟩

private theorem w1369_minStableJoin_le {P : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : ∀ S : Subgroup W, w1369_MinStable P S → S ≤ V) : w1369_minStableJoin P ≤ V := by
  unfold w1369_minStableJoin
  exact iSup_le (fun S : {T : Subgroup W // w1369_MinStable P T} => hV S.1 S.2)

private theorem w1369_minStableJoin_eq_top_of_complemented {P : Subgroup (MulAut W)}
    (hP : w1369_Complemented P) : w1369_minStableJoin P = ⊤ := by
  refine eq_top_iff.mpr ?_
  by_contra hnot
  have hZne : w1369_minStableJoin P ≠ ⊤ := fun hZ => hnot (hZ ▸ le_rfl)
  have hlt : w1369_minStableJoin P < ⊤ := lt_top_iff_ne_top.mpr hZne
  obtain ⟨Q, hQstab, hsup, hinf⟩ := hP _ (w1369_minStableJoin_stable P)
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    rw [hQbot, sup_bot_eq] at hsup
    rw [hsup] at hlt
    exact lt_irrefl _ hlt
  haveI : Fintype (Subgroup W) := Fintype.ofFinite _
  obtain ⟨S, hSmin⟩ := exists_minimal_of_wellFoundedLT
    (fun T : Subgroup W => StableUnder P T ∧ T ≤ Q ∧ T ≠ ⊥) ⟨Q, hQstab, le_rfl, hQne⟩
  have hSstab : StableUnder P S := hSmin.1.1
  have hSQ : S ≤ Q := hSmin.1.2.1
  have hSne : S ≠ ⊥ := hSmin.1.2.2
  have hSminimal : ∀ T : Subgroup W, StableUnder P T → T ≤ S → T = ⊥ ∨ T = S := by
    intro T hT hTS
    by_cases hTb : T = ⊥
    · exact Or.inl hTb
    · exact Or.inr (le_antisymm hTS (hSmin.2 ⟨hT, hTS.trans hSQ, hTb⟩ hTS))
  have hSm : w1369_MinStable P S := ⟨hSstab, hSne, hSminimal⟩
  have hSZ : S ≤ w1369_minStableJoin P := w1369_le_minStableJoin hSm
  have hSbot : S ≤ ⊥ := by
    have hle : S ≤ w1369_minStableJoin P ⊓ Q := le_inf hSZ hSQ
    rwa [hinf] at hle
  exact hSne (le_bot_iff.mp hSbot)

private theorem w1369_complemented_of_minStableJoin_eq_top {P : Subgroup (MulAut W)}
    (hP : w1369_minStableJoin P = ⊤) : w1369_Complemented P := by
  intro B hB
  haveI : Fintype (Subgroup W) := Fintype.ofFinite _
  obtain ⟨C, hCmax⟩ := exists_maximal_of_wellFoundedGT
    (fun C : Subgroup W => StableUnder P C ∧ B ⊓ C = ⊥)
    ⟨⊥, (fun x hx w hw => by
      rw [Subgroup.mem_bot] at hw
      rw [hw]
      simp), by simp⟩
  have hCstab : StableUnder P C := hCmax.1.1
  have hCinf : B ⊓ C = ⊥ := hCmax.1.2
  have hsup : B ⊔ C = ⊤ := by
    by_contra hne
    have hnotall : ¬ ∀ S : Subgroup W, w1369_MinStable P S → S ≤ B ⊔ C := by
      intro hall
      have hle : w1369_minStableJoin P ≤ B ⊔ C := w1369_minStableJoin_le hall
      rw [hP] at hle
      exact hne (le_antisymm le_top hle)
    obtain ⟨S, hS⟩ := not_forall.mp hnotall
    obtain ⟨hSm, hSnotle⟩ := not_imp.mp hS
    have hBSinf : S ⊓ (B ⊔ C) = ⊥ := by
      have hstab := w1369_stableUnder_inf hSm.1 (w1369_stableUnder_sup hB hCstab)
      rcases hSm.2.2 _ hstab inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right) hSnotle
    have hC'stab : StableUnder P (C ⊔ S) := w1369_stableUnder_sup hCstab hSm.1
    have hC'inf : B ⊓ (C ⊔ S) = ⊥ := by
      rw [eq_bot_iff]
      intro b hb
      obtain ⟨hbB, hbCS⟩ := hb
      obtain ⟨c, hc, s, hs, hcs⟩ := Subgroup.mem_sup.mp hbCS
      have hsBC : s ∈ B ⊔ C := by
        have hs_eq : s = c⁻¹ * b := by rw [← hcs]; group
        rw [hs_eq]
        exact (B ⊔ C).mul_mem (Subgroup.mem_sup_right (C.inv_mem hc))
          (Subgroup.mem_sup_left hbB)
      have hs_bot : s ∈ (⊥ : Subgroup W) := by
        rw [← hBSinf]
        exact ⟨hs, hsBC⟩
      rw [Subgroup.mem_bot] at hs_bot
      have hb_eq : b = c := by rw [← hcs, hs_bot, mul_one]
      rw [hb_eq] at hbB ⊢
      have hmem : c ∈ B ⊓ C := ⟨hbB, hc⟩
      rwa [hCinf] at hmem
    have hltCS : C < C ⊔ S := by
      refine lt_of_le_of_ne le_sup_left ?_
      intro heq
      have hSC : S ≤ C := by
        rw [heq]
        exact le_sup_right
      exact hSnotle (hSC.trans le_sup_right)
    have hC'le : C ⊔ S ≤ C := hCmax.2 ⟨hC'stab, hC'inf⟩ le_sup_left
    exact hltCS.ne (le_antisymm le_sup_left hC'le)
  exact ⟨C, hCstab, hsup, hCinf⟩

private theorem w1369_minStable_le_minStableJoin_of_normal {N M : Subgroup (MulAut W)}
    (hNM : N ≤ M) (hnorm : (N.subgroupOf M).Normal)
    {S : Subgroup W} (hS : w1369_MinStable M S) :
    S ≤ w1369_minStableJoin N := by
  have hNS : StableUnder N S := fun n hn s hs => hS.1 n (hNM hn) s hs
  haveI : Fintype (Subgroup W) := Fintype.ofFinite _
  obtain ⟨T, hTmin⟩ := exists_minimal_of_wellFoundedLT
    (fun T : Subgroup W => StableUnder N T ∧ T ≤ S ∧ T ≠ ⊥)
    ⟨S, hNS, le_rfl, hS.2.1⟩
  have hTN : StableUnder N T := hTmin.1.1
  have hTS : T ≤ S := hTmin.1.2.1
  have hTne : T ≠ ⊥ := hTmin.1.2.2
  have hTmin' : ∀ U : Subgroup W, StableUnder N U → U ≤ T → U = ⊥ ∨ U = T := by
    intro U hU hUT
    by_cases hUb : U = ⊥
    · exact Or.inl hUb
    · exact Or.inr (le_antisymm hUT (hTmin.2 ⟨hU, hUT.trans hTS, hUb⟩ hUT))
  have hconj : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
    intro m hm n hn
    have hmem : (⟨n, hNM hn⟩ : M) ∈ N.subgroupOf M := Subgroup.mem_subgroupOf.mpr hn
    have hc := hnorm.conj_mem (⟨n, hNM hn⟩ : M) hmem (⟨m, hm⟩ : M)
    exact Subgroup.mem_subgroupOf.mp hc
  have hmapN : ∀ m : M, StableUnder N (Subgroup.map ((m : MulAut W) : W →* W) T) := by
    intro m n hn x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hmn : (m : MulAut W)⁻¹ * n * (m : MulAut W) ∈ N := by
      have h := hconj (m : MulAut W)⁻¹ (M.inv_mem m.2) n hn
      simpa only [inv_inv] using h
    refine ⟨((m : MulAut W)⁻¹ * n * (m : MulAut W)) t, hTN _ hmn t ht, ?_⟩
    show (m : MulAut W) (((m : MulAut W)⁻¹ * n * (m : MulAut W)) t) =
      n ((m : MulAut W) t)
    rw [MulAut.mul_apply, MulAut.mul_apply]
    exact MulEquiv.apply_symm_apply (m : MulAut W) (n ((m : MulAut W) t))
  have hmapMin : ∀ m : M,
      w1369_MinStable N (Subgroup.map ((m : MulAut W) : W →* W) T) := by
    intro m
    refine ⟨hmapN m, ?_, ?_⟩
    · intro hbot
      have h1 : Subgroup.map (((m : MulAut W)⁻¹ : MulAut W) : W →* W)
          (Subgroup.map ((m : MulAut W) : W →* W) T) = T := by
        rw [Subgroup.map_map]
        rw [show ((((m : MulAut W)⁻¹ : MulAut W) : W →* W).comp
            ((m : MulAut W) : W →* W)) = MonoidHom.id W by
          ext t; simp]
        rw [Subgroup.map_id]
      rw [hbot, Subgroup.map_bot] at h1
      exact hTne h1.symm
    · intro U hU hUle
      by_cases hUb : U = ⊥
      · exact Or.inl hUb
      · right
        let U' : Subgroup W :=
          Subgroup.map (((m : MulAut W)⁻¹ : MulAut W) : W →* W) U
        have hU'N : StableUnder N U' := by
          intro n hn x hx
          obtain ⟨u, hu, rfl⟩ := hx
          have hmn : (m : MulAut W) * n * (m : MulAut W)⁻¹ ∈ N :=
            hconj (m : MulAut W) m.2 n hn
          refine ⟨((m : MulAut W) * n * (m : MulAut W)⁻¹) u, hU _ hmn u hu, ?_⟩
          show (m : MulAut W)⁻¹ (((m : MulAut W) * n * (m : MulAut W)⁻¹) u) =
            n ((m : MulAut W)⁻¹ u)
          rw [MulAut.mul_apply, MulAut.mul_apply]
          exact MulEquiv.symm_apply_apply (m : MulAut W) (n ((m : MulAut W)⁻¹ u))
        have hU'le : U' ≤ T := by
          have h := Subgroup.map_mono
            (f := (((m : MulAut W)⁻¹ : MulAut W) : W →* W)) hUle
          have h2 : Subgroup.map (((m : MulAut W)⁻¹ : MulAut W) : W →* W)
              (Subgroup.map ((m : MulAut W) : W →* W) T) = T := by
            rw [Subgroup.map_map]
            rw [show ((((m : MulAut W)⁻¹ : MulAut W) : W →* W).comp
                ((m : MulAut W) : W →* W)) = MonoidHom.id W by
              ext t; simp]
            rw [Subgroup.map_id]
          rwa [h2] at h
        have hUU' : Subgroup.map ((m : MulAut W) : W →* W) U' = U := by
          rw [Subgroup.map_map]
          rw [show (((m : MulAut W) : W →* W).comp
              (((m : MulAut W)⁻¹ : MulAut W) : W →* W)) = MonoidHom.id W by
          ext t; simp]
          rw [Subgroup.map_id]
        rcases hTmin' U' hU'N hU'le with hU'bot | hU'T
        · exact absurd (by rw [← hUU', hU'bot, Subgroup.map_bot]) hUb
        · exact (hUU'.symm.trans (congrArg _ hU'T))
  let U : Subgroup W := ⨆ (m : M), Subgroup.map ((m : MulAut W) : W →* W) T
  have hUstab : StableUnder M U := by
    intro a ha u hu
    refine Subgroup.iSup_induction
      (fun m : M => Subgroup.map ((m : MulAut W) : W →* W) T) (C := fun y => a y ∈ U)
      hu ?_ ?_ ?_
    · intro m y hy
      obtain ⟨t, ht, rfl⟩ := hy
      refine Subgroup.mem_iSup_of_mem
        (⟨(a : MulAut W) * (m : MulAut W), M.mul_mem ha m.2⟩ : M) ?_
      refine ⟨t, ht, ?_⟩
      show ((a : MulAut W) * (m : MulAut W)) t = a ((m : MulAut W) t)
      rw [MulAut.mul_apply]
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro y z hy hz
      rw [map_mul]
      exact Subgroup.mul_mem _ hy hz
  have hUleS : U ≤ S := by
    refine iSup_le (fun m : M => ?_)
    rintro x ⟨t, ht, rfl⟩
    exact hS.1 (m : MulAut W) m.2 t (hTS ht)
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hTU : T ≤ U := by
      intro t ht
      exact Subgroup.mem_iSup_of_mem (1 : M) ⟨t, ht, by simp⟩
    exact hTne (le_bot_iff.mp (hbot ▸ hTU))
  have hUS : U = S := by
    rcases hS.2.2 U hUstab hUleS with h | h
    · exact absurd h hUne
    · exact h
  rw [← hUS]
  exact iSup_le (fun m : M => w1369_le_minStableJoin (hmapMin m))

private theorem w1369_minStableJoin_eq_top_of_normal {N M : Subgroup (MulAut W)}
    (hNM : N ≤ M) (hnorm : (N.subgroupOf M).Normal)
    (hM : w1369_minStableJoin M = ⊤) : w1369_minStableJoin N = ⊤ := by
  rw [eq_top_iff, ← hM]
  exact w1369_minStableJoin_le
    (fun S hS => w1369_minStable_le_minStableJoin_of_normal hNM hnorm hS)

private theorem w1369_complemented_of_normal {N M : Subgroup (MulAut W)}
    (hNM : N ≤ M) (hnorm : (N.subgroupOf M).Normal)
    (hM : w1369_Complemented M) : w1369_Complemented N :=
  w1369_complemented_of_minStableJoin_eq_top
    (w1369_minStableJoin_eq_top_of_normal hNM hnorm
      (w1369_minStableJoin_eq_top_of_complemented hM))

private theorem w1369_complemented_of_subnormal {H G : Subgroup (MulAut W)}
    (h : CFSG.Open.IsSubnormal H G) : w1369_Complemented G → w1369_Complemented H := by
  induction h with
  | refl H => exact id
  | step hHM hN hMK ih => exact fun hM => w1369_complemented_of_normal hHM hN (ih hM)

private theorem w1369_sup_subgroupOf_normal {A B X G : Subgroup (MulAut W)}
    (hAB : A ≤ B) (hBG : B ≤ G) (hXG : X ≤ G)
    (hnA : (A.subgroupOf B).Normal)
    (hnX : ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    ((A ⊔ X).subgroupOf (B ⊔ X)).Normal := by
  have hXnorm : G ≤ Subgroup.normalizer X := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hnX g hg x hx, fun hx => by
      have h := hnX g⁻¹ (G.inv_mem hg) (g * x * g⁻¹) hx
      simpa [mul_assoc] using h⟩
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le_sup_right hAB X)).mpr ?_
  refine sup_le ?_ ?_
  · intro b hb
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hA : A.map (MulAut.conj b) = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hAB).mp hnA hb)
    have hX : X.map (MulAut.conj b) = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXnorm (hBG hb))
    rw [Subgroup.map_sup, hA, hX]
  · exact le_trans le_sup_right Subgroup.le_normalizer

private theorem w1369_isSubnormal_sup {K G X : Subgroup (MulAut W)}
    (h : CFSG.Open.IsSubnormal K G) (hXG : X ≤ G)
    (hnX : ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    CFSG.Open.IsSubnormal (K ⊔ X) G := by
  have hmain : G ≤ G → CFSG.Open.IsSubnormal (K ⊔ X) (G ⊔ X) :=
    CFSG.Open.IsSubnormal.rec
      (motive := fun A B _ => B ≤ G → CFSG.Open.IsSubnormal (A ⊔ X) (B ⊔ X))
      (fun A _ => CFSG.Open.IsSubnormal.refl (A ⊔ X))
      (fun {A B C} hAB hN hBC ih hCG => by
        have hBG : B ≤ G := (CFSG.Open.IsSubnormal.le hBC).trans hCG
        exact CFSG.Open.IsSubnormal.trans
          (CFSG.Open.IsSubnormal.step (sup_le_sup_right hAB X)
            (w1369_sup_subgroupOf_normal hAB hBG hXG hN hnX)
            (CFSG.Open.IsSubnormal.refl _))
          (ih hCG))
      h
  simpa [sup_eq_left.mpr hXG] using hmain (le_refl G)

private theorem w1369_complemented_of_irr {P : Subgroup (MulAut W)}
    (hirr : ∀ Z : Subgroup W, StableUnder P Z → Z = ⊥ ∨ Z = ⊤) :
    w1369_Complemented P := by
  intro B hB
  rcases hirr B hB with h | h
  · rw [h]
    exact ⟨⊤, (fun x hx w hw => Subgroup.mem_top w), by simp, by simp⟩
  · rw [h]
    exact ⟨⊥, (fun x hx w hw => by
      rw [Subgroup.mem_bot] at hw
      rw [hw]
      simp), by simp, by simp⟩

theorem Std139.complete_reducibility_KX (hw2 : ∀ w : W, w ^ 2 = 1) (S : Std139 G X D s Y n)
    {K : Subgroup (MulAut W)} (hK : IsComponentOf K G) {B : Subgroup W}
    (hBK : StableUnder K B) (hBX : StableUnder X B) :
    ∃ C : Subgroup W, StableUnder K C ∧ StableUnder X C ∧ B ⊔ C = ⊤ ∧ B ⊓ C = ⊥ := by
  have hXG : X ≤ G := S.XG
  have hnX : ∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X := S.Xnorm
  have hGN : CFSG.Open.IsSubnormal (K ⊔ X) G := w1369_isSubnormal_sup hK.2.1 hXG hnX
  have hcompH : w1369_Complemented (K ⊔ X) :=
    w1369_complemented_of_subnormal hGN (w1369_complemented_of_irr S.irr)
  have hBsup : StableUnder (K ⊔ X) B := by
    have hK : K ≤ stabSub B := by
      intro k hk
      show ∀ b : W, k b ∈ B ↔ b ∈ B
      intro b
      exact ⟨fun hkb => (show k⁻¹ (k b) = b from MulEquiv.symm_apply_apply k b) ▸
        hBK k⁻¹ (K.inv_mem hk) (k b) hkb, fun hb => hBK k hk b hb⟩
    have hX : X ≤ stabSub B := by
      intro x hx
      show ∀ b : W, x b ∈ B ↔ b ∈ B
      intro b
      exact ⟨fun hxb => (show x⁻¹ (x b) = b from MulEquiv.symm_apply_apply x b) ▸
        hBX x⁻¹ (X.inv_mem hx) (x b) hxb, fun hb => hBX x hx b hb⟩
    have hle : K ⊔ X ≤ stabSub B := sup_le hK hX
    intro m hm b hb
    exact ((mem_stabSub.mp (hle hm)) b).mpr hb
  obtain ⟨C, hCsup, hsup, hinf⟩ := hcompH B hBsup
  exact ⟨C, (fun k hk c hc => hCsup k (Subgroup.mem_sup_left hk) c hc),
    (fun x hx c hc => hCsup x (Subgroup.mem_sup_right hx) c hc), hsup, hinf⟩

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
