module

public import CFSG.LocalAnalysis.StandardType.GGHalfGraphClosure
public import CFSG.LocalAnalysis.StandardType.GGHalfGraphAmalgam

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule

namespace GGHalfCtx

private theorem ggHalfGraphE6_one_add_one_f2 : (1 : F2) + 1 = 0 := by
  have h2 : (2 : F2) = 0 := CFSG.StandardType.GGHalf.gf2_two
  linear_combination h2

private theorem ggHalfGraphE6_tv_self {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) * SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, ggHalfGraphE6_one_add_one_f2]
  exact SpecialLinearGroup.transvection_coeff_zero hij

private theorem ggHalfGraphE6_transvection_ne_one {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) ≠ 1 := by
  intro h
  have hc := congrArg (fun g : SpecialLinearGroup (Fin N) F2 =>
      (g : Matrix (Fin N) (Fin N) F2) i j) h
  rw [SpecialLinearGroup.transvection_coe] at hc
  simp [Matrix.transvection] at hc

private theorem ggHalfGraphE6_slE_zero_one_ne_one : slE (0 : Fin 6) 1 ≠ 1 := by
  intro h
  have h01 : (0 : Fin 6) ≠ 1 := by decide
  have : SpecialLinearGroup.transvection h01 (1 : F2) = 1 := by
    simpa only [slE, dif_neg h01] using h
  exact ggHalfGraphE6_transvection_ne_one h01 this

private theorem ggHalfGraphE6_omegaBlock_eq_tv (k : Fin 5) :
    omegaBlock 5 k =
      SpecialLinearGroup.transvection (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
        (1 : F2) *
      SpecialLinearGroup.transvection
        ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne).symm 1 := by
  have hkj : k.castSucc ≠ k.succ := (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
  have hjk : k.succ ≠ k.castSucc := hkj.symm
  set x : SpecialLinearGroup (Fin 6) F2 := SpecialLinearGroup.transvection hkj 1 with hx
  set y : SpecialLinearGroup (Fin 6) F2 := SpecialLinearGroup.transvection hjk 1 with hy
  have hxyx : weylRep 5 F2 k = x * y * x := by
    rw [weylRep_eq_slPerm]
    rw [slPerm_swap_eq_transvections gf2_two hkj, ← hx, ← hy]
  have hxx : x * x = 1 := ggHalfGraphE6_tv_self hkj
  calc omegaBlock 5 k
      = weylRep 5 F2 k *
          SpecialLinearGroup.transvection
            (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne 1 := rfl
    _ = x * y * x * x := by rw [hxyx, ← hx]
    _ = x * y * (x * x) := by group
    _ = x * y * 1 := by rw [hxx]
    _ = x * y := by rw [mul_one]

private theorem ggHalfGraphE6_omegaBlock_eq_slE_mul (k : Fin 5) :
    omegaBlock 5 k = slE k.castSucc k.succ * slE k.succ k.castSucc := by
  have hkj : k.castSucc ≠ k.succ := (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne
  have hjk : k.succ ≠ k.castSucc := hkj.symm
  rw [ggHalfGraphE6_omegaBlock_eq_tv k, slE, slE, dif_neg hkj, dif_neg hjk]

private theorem ggHalfGraphE6_lab_surj {b : GGHalfBlk} {a : Fin 8} (ha : b.Lab a) :
    ∃ c : Fin 6, b.lab c = a := by
  cases b
  · simp only [GGHalfBlk.Lab] at ha
    refine ⟨⟨a.val, ha⟩, ?_⟩
    ext
    simp [GGHalfBlk.lab, GGHalfBlk.off]
  · simp only [GGHalfBlk.Lab] at ha
    refine ⟨⟨a.val - 2, by omega⟩, ?_⟩
    ext
    simp only [GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk]
    omega
  · simp only [GGHalfBlk.Lab] at ha
    refine ⟨⟨a.val - 2, by omega⟩, ?_⟩
    ext
    simp only [GGHalfBlk.lab, GGHalfBlk.off, Fin.val_mk]
    omega

private theorem ggHalfGraphE6_f2_eq_zero_or_one (z : F2) : z = 0 ∨ z = 1 := by
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  by_cases hz : z = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq z hz).trans (huniq 1 one_ne_zero).symm)

private theorem ggHalfGraphE6_closure_xm_eq_top
    {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type*) [Field k] :
    Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : k),
      g = hV.xm k (Pi.single i 1) c ∨ g = hV.xm k (-Pi.single i 1) c} = ⊤ := by
  set S := Subgroup.closure {g | ∃ (i : Fin τ.rank) (c : k),
      g = hV.xm k (Pi.single i 1) c ∨ g = hV.xm k (-Pi.single i 1) c}
  have hn : ∀ i, hV.nm k i ∈ S := fun i =>
    mul_mem (mul_mem (Subgroup.subset_closure ⟨i, _, Or.inl rfl⟩)
      (Subgroup.subset_closure ⟨i, _, Or.inr rfl⟩)) (Subgroup.subset_closure ⟨i, _, Or.inl rfl⟩)
  have hx : ∀ γ, IsRoot τ γ → ∀ c : k, hV.xm k γ c ∈ S := by
    intro γ hγ
    induction hγ with
    | basis j => exact fun c => Subgroup.subset_closure ⟨j, c, Or.inl rfl⟩
    | @reflect i v hv ih =>
      intro c
      obtain ⟨σ, hσ, h⟩ := hV.nm_conj_xm k hv i
      have e : hV.xm k (reflect τ i v) c = hV.nm k i * hV.xm k v (σ * c) * (hV.nm k i)⁻¹ := by
        rw [h, ← mul_assoc, hσ.mul_self, one_mul]
      rw [e]
      exact mul_mem (mul_mem (hn i) (ih _)) (inv_mem (hn i))
  rw [eq_top_iff, ← hV.iSup_rootGroup k]
  refine iSup₂_le fun γ hγ => ?_
  intro g hg
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hg
  exact hx γ hγ c

private theorem ggHalfGraphE6_closure_simpleRoot_eq_top :
    Subgroup.closure {g : GGE6Two | ∃ i : Fin (Tag.rank .E6),
      g = ggE6x (GGHalfE6Model.simpleRoot i) ∨
        g = ggE6x (-(GGHalfE6Model.simpleRoot i))} = ⊤ := by
  have h := ggHalfGraphE6_closure_xm_eq_top
    (CFSG.LieType.Steinberg.Minuscule.e6Data_valid) (GaloisField 2 1)
  rw [eq_top_iff, ← h, Subgroup.closure_le]
  rintro z ⟨i, c, hz⟩
  rcases hz with rfl | rfl
  · rcases ggHalfGraphE6_f2_eq_zero_or_one c with rfl | rfl
    · rw [CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm_zero]
      exact one_mem _
    · exact Subgroup.subset_closure ⟨i, Or.inl rfl⟩
  · rcases ggHalfGraphE6_f2_eq_zero_or_one c with rfl | rfl
    · rw [CFSG.LieType.Steinberg.Minuscule.e6Data_valid.xm_zero]
      exact one_mem _
    · exact Subgroup.subset_closure ⟨i, Or.inr rfl⟩

private theorem ggHalfGraphE6_frameOK {m : GGHalfE6Model} (hm : m.Good) (b : GGHalfBlk) :
    m.FrameOK b := by
  cases b
  · exact hm.1
  · exact hm.2.1
  · exact hm.2.2.1

private theorem ggHalfGraphE6_neg_mem_Y {m : GGHalfE6Model} {b : GGHalfBlk} {r : GGE6Root}
    (hr : r ∈ m.Y b) (hfr : m.FrameOK b) : -r ∈ m.Y b := by
  obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hr
  exact ⟨d, c, hd, hc, hcd.symm, hfr.2.1 c d hc hd hcd⟩

private theorem ggHalfGraphE6_exists_lab_frame {m : GGHalfE6Model} {b : GGHalfBlk} {r : GGE6Root}
    (hr : r ∈ m.Y b) : ∃ c d : Fin 6, c ≠ d ∧ m.frame b (b.lab c) (b.lab d) = r := by
  obtain ⟨c₀, d₀, hc₀, hd₀, hcd₀, hframe⟩ := hr
  obtain ⟨c, hc⟩ := ggHalfGraphE6_lab_surj hc₀
  obtain ⟨d, hd⟩ := ggHalfGraphE6_lab_surj hd₀
  refine ⟨c, d, ?_, ?_⟩
  · intro hcd; exact hcd₀ (by rw [← hc, ← hd, hcd])
  · rw [hc, hd, hframe]

private theorem ggHalfGraphE6_conj_map_le {G : Type} [Group G] {H P : Subgroup G} {g : G}
    (hg : g ∈ P) (hH : H ≤ P) : H.map (MulAut.conj g).toMonoidHom ≤ P := by
  rintro x ⟨k, hk, rfl⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact P.mul_mem (P.mul_mem hg (hH hk)) (P.inv_mem hg)

theorem exists_e6_of_graph
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hg : ¬ GGHalfAlphaInner φ₁ φ₂)
    (m : GGHalfE6Model) (hm : m.Good) :
    ∃ φ : GGE6Two →* G, Function.Injective φ ∧ φ.range ≤ ggG0 p B x L D J ∧
      (∀ c d : Fin 6, c ≠ d →
        φ (ggE6x (m.frame .L (GGHalfBlk.L.lab c) (GGHalfBlk.L.lab d))) = φ₁ (slE c d)) ∧
      (∀ c d : Fin 6, c ≠ d →
        φ (ggE6x (m.frame .K (GGHalfBlk.K.lab c) (GGHalfBlk.K.lab d))) = φ₂ (slE c d)) ∧
      φ (ggE6u (m.frame .L 0 1)) = vElt φ₁ ∧ φ (ggE6u (m.frame .K 6 7)) = wElt φ₂ ∧
      m.J0.map φ = J := by
  have hΦ := GGHalfCtx.frames_agree h hg m hm
  have hnt : ∃ c d : Fin 6, c ≠ d ∧ ggHalfBlockHom φ₁ φ₂ .L (slE c d) ≠ 1 := by
    refine ⟨0, 1, by decide, ?_⟩
    show φ₁ (slE (0 : Fin 6) 1) ≠ 1
    intro h1
    exact ggHalfGraphE6_slE_zero_one_ne_one (h.coords.inj₁ (by rw [h1, map_one]))
  obtain ⟨φ, hinj, hbase⟩ := exists_e6_hom_of_frames m hm (ggHalfBlockHom φ₁ φ₂) hΦ hnt
  have hsound := GGHalfCtx.closure_sound h hg m hm φ hbase
  have hL : ∀ c d : Fin 6, c ≠ d →
      φ (ggE6x (m.frame .L (GGHalfBlk.L.lab c) (GGHalfBlk.L.lab d))) = φ₁ (slE c d) := by
    intro c d hcd
    have hh := hsound .L c d hcd
    rwa [show ggHalfBlockHom φ₁ φ₂ .L = φ₁ from rfl] at hh
  have hK : ∀ c d : Fin 6, c ≠ d →
      φ (ggE6x (m.frame .K (GGHalfBlk.K.lab c) (GGHalfBlk.K.lab d))) = φ₂ (slE c d) := by
    intro c d hcd
    have hh := hsound .K c d hcd
    rwa [show ggHalfBlockHom φ₁ φ₂ .K = φ₂ from rfl] at hh
  have hnbr : GGNbr p B x D J y K := h.nbr.2.2.2.2.1
  have hblockle : ∀ b : GGHalfBlk, (ggHalfBlockHom φ₁ φ₂ b).range ≤ ggG0 p B x L D J := by
    intro b
    cases b
    · rw [show ggHalfBlockHom φ₁ φ₂ .L = φ₁ from rfl, h.coords.range₁]
      exact le_ggG0_left p B x L D J
    · rw [show ggHalfBlockHom φ₁ φ₂ .K = φ₂ from rfl, h.coords.range₂]
      exact le_ggG0_of_ggNbr hnbr
    · rw [show ggHalfBlockHom φ₁ φ₂ .M =
          (MulAut.conj (gElt φ₁)).toMonoidHom.comp φ₂ from rfl,
        MonoidHom.range_comp, h.coords.range₂]
      have hgL : gElt φ₁ ∈ L := by
        rw [← h.coords.range₁]
        exact ⟨_, rfl⟩
      exact ggHalfGraphE6_conj_map_le (G := G)
        (le_ggG0_left p B x L D J hgL) (le_ggG0_of_ggNbr hnbr)
  have hsimple (i : Fin (Tag.rank .E6)) :
      φ (ggE6x (GGHalfE6Model.simpleRoot i)) ∈ ggG0 p B x L D J := by
    obtain ⟨b, hb, -⟩ := hm.2.2.2.2.2.2.2.2.1 i i
    obtain ⟨c, d, hcd, hframe⟩ := ggHalfGraphE6_exists_lab_frame hb
    rw [← hframe, hsound b c d hcd]
    exact hblockle b (MonoidHom.mem_range.mpr ⟨slE c d, rfl⟩)
  have hnegSimple (i : Fin (Tag.rank .E6)) :
      φ (ggE6x (-(GGHalfE6Model.simpleRoot i))) ∈ ggG0 p B x L D J := by
    obtain ⟨b, hb, -⟩ := hm.2.2.2.2.2.2.2.2.1 i i
    have hnb : -(GGHalfE6Model.simpleRoot i) ∈ m.Y b :=
      ggHalfGraphE6_neg_mem_Y hb (ggHalfGraphE6_frameOK hm b)
    obtain ⟨c, d, hcd, hframe⟩ := ggHalfGraphE6_exists_lab_frame hnb
    rw [← hframe, hsound b c d hcd]
    exact hblockle b (MonoidHom.mem_range.mpr ⟨slE c d, rfl⟩)
  have hrange : φ.range ≤ ggG0 p B x L D J := by
    have hgen := ggHalfGraphE6_closure_simpleRoot_eq_top
    have hmem : ∀ u : GGE6Two,
        u ∈ Subgroup.closure {g : GGE6Two | ∃ i : Fin (Tag.rank .E6),
          g = ggE6x (GGHalfE6Model.simpleRoot i) ∨
            g = ggE6x (-(GGHalfE6Model.simpleRoot i))} → φ u ∈ ggG0 p B x L D J := by
      intro u hu
      refine Subgroup.closure_induction (p := fun u _ => φ u ∈ ggG0 p B x L D J)
        ?_ ?_ ?_ ?_ hu
      · rintro z ⟨i, hz | hz⟩
        · rw [hz]; exact hsimple i
        · rw [hz]; exact hnegSimple i
      · rw [map_one]; exact one_mem _
      · intro a b _ _ iha ihb; rw [map_mul]; exact mul_mem iha ihb
      · intro a _ iha; rw [map_inv]; exact inv_mem iha
    rintro z ⟨u, rfl⟩
    exact hmem u (by rw [hgen]; trivial)
  refine ⟨φ, hinj, hrange, ?_, ?_, ?_, ?_, ?_⟩
  · exact hL
  · exact hK
  ·
    have h0 : GGHalfBlk.Lab .L (0 : Fin 8) := by
      change (0 : Fin 8).val < 6
      decide
    have h1 : GGHalfBlk.Lab .L (1 : Fin 8) := by
      change (1 : Fin 8).val < 6
      decide
    have hL01 : φ (ggE6x (m.frame .L 0 1)) = φ₁ (slE (0 : Fin 6) 1) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hL 0 1 (by decide)
    have hL10 : φ (ggE6x (m.frame .L 1 0)) = φ₁ (slE (1 : Fin 6) 0) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hL 1 0 (by decide)
    have hneg : -(m.frame .L 0 1) = m.frame .L 1 0 := (hm.1.2.1 0 1 h0 h1 (by decide)).symm
    calc φ (ggE6u (m.frame .L 0 1))
        = φ (ggE6x (m.frame .L 0 1) * ggE6x (-(m.frame .L 0 1))) := rfl
      _ = φ (ggE6x (m.frame .L 0 1)) * φ (ggE6x (-(m.frame .L 0 1))) := map_mul _ _ _
      _ = φ (ggE6x (m.frame .L 0 1)) * φ (ggE6x (m.frame .L 1 0)) := by rw [hneg]
      _ = φ₁ (slE (0 : Fin 6) 1) * φ₁ (slE (1 : Fin 6) 0) := by rw [hL01, hL10]
      _ = φ₁ (slE (0 : Fin 6) 1 * slE (1 : Fin 6) 0) := (map_mul φ₁ _ _).symm
      _ = φ₁ (omegaBlock 5 (0 : Fin 5)) := by
        rw [show slE (0 : Fin 6) 1 * slE (1 : Fin 6) 0 =
              slE (0 : Fin 5).castSucc (0 : Fin 5).succ *
                slE (0 : Fin 5).succ (0 : Fin 5).castSucc from rfl,
          ← ggHalfGraphE6_omegaBlock_eq_slE_mul 0]
      _ = vElt φ₁ := rfl
  ·
    have h6 : GGHalfBlk.Lab .K (6 : Fin 8) := by
      change 2 ≤ (6 : Fin 8).val
      decide
    have h7 : GGHalfBlk.Lab .K (7 : Fin 8) := by
      change 2 ≤ (7 : Fin 8).val
      decide
    have hK45 : φ (ggE6x (m.frame .K 6 7)) = φ₂ (slE (4 : Fin 6) 5) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hK 4 5 (by decide)
    have hK54 : φ (ggE6x (m.frame .K 7 6)) = φ₂ (slE (5 : Fin 6) 4) := by
      simpa [GGHalfBlk.lab, GGHalfBlk.off] using hK 5 4 (by decide)
    have hnegK : -(m.frame .K 6 7) = m.frame .K 7 6 := (hm.2.1.2.1 6 7 h6 h7 (by decide)).symm
    calc φ (ggE6u (m.frame .K 6 7))
        = φ (ggE6x (m.frame .K 6 7) * ggE6x (-(m.frame .K 6 7))) := rfl
      _ = φ (ggE6x (m.frame .K 6 7)) * φ (ggE6x (-(m.frame .K 6 7))) := map_mul _ _ _
      _ = φ (ggE6x (m.frame .K 6 7)) * φ (ggE6x (m.frame .K 7 6)) := by rw [hnegK]
      _ = φ₂ (slE (4 : Fin 6) 5) * φ₂ (slE (5 : Fin 6) 4) := by rw [hK45, hK54]
      _ = φ₂ (slE (4 : Fin 6) 5 * slE (5 : Fin 6) 4) := (map_mul φ₂ _ _).symm
      _ = φ₂ (omegaBlock 5 (4 : Fin 5)) := by
        rw [show slE (4 : Fin 6) 5 * slE (5 : Fin 6) 4 =
              slE (4 : Fin 5).castSucc (4 : Fin 5).succ *
                slE (4 : Fin 5).succ (4 : Fin 5).castSucc from rfl,
          ← ggHalfGraphE6_omegaBlock_eq_slE_mul 4]
      _ = wElt φ₂ := rfl
  ·
    let S0 : Set GGE6Two := {g | ∃ c d : Fin 8,
      2 ≤ c.val ∧ c.val < 6 ∧ 2 ≤ d.val ∧ d.val < 6 ∧ c ≠ d ∧ g = ggE6x (m.frame .L c d)}
    let S1 : Set (SpecialLinearGroup (Fin 6) F2) := {t | ∃ c d : Fin 6,
      2 ≤ c.val ∧ 2 ≤ d.val ∧ c ≠ d ∧ t = slE c d}
    have hS1 : Subgroup.closure S1 = slOn 6 {i : Fin 6 | 2 ≤ i.val} := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro t ⟨c, d, hc, hd, hcd, rfl⟩
        rw [slE, dif_neg hcd]
        exact transvection_mem_slOn hcd 1 hc hd
      · rw [slOn, Subgroup.closure_le]
        rintro t ⟨a, b, hab, e, ha, hb, rfl⟩
        rcases ggHalfGraphE6_f2_eq_zero_or_one e with rfl | rfl
        · rw [SpecialLinearGroup.transvection_coeff_zero]
          exact one_mem _
        · refine Subgroup.subset_closure ⟨a, b, ha, hb, hab, ?_⟩
          rw [slE, dif_neg hab]
    have hJeq : J = Subgroup.closure (φ₁ '' S1) := by
      rw [← h.coords.rangeJ, MonoidHom.range_comp,
        show (slLower2Hom 3).range = slOn 6 {i : Fin 6 | 2 ≤ i.val} from range_slLower2Hom 3,
        ← hS1, MonoidHom.map_closure]
    have hmapJ0 : m.J0.map φ = Subgroup.closure (φ '' S0) := by
      rw [show m.J0 = Subgroup.closure S0 from rfl, MonoidHom.map_closure]
    have hsub0 : φ '' S0 ⊆ Subgroup.closure (φ₁ '' S1) := by
      rintro y ⟨g, hg, rfl⟩
      obtain ⟨c, d, hc2, hclt, hd2, hdlt, hcd, rfl⟩ := hg
      let c' : Fin 6 := ⟨c.val, hclt⟩
      let d' : Fin 6 := ⟨d.val, hdlt⟩
      have hcd' : c' ≠ d' := by
        intro h; exact hcd (Fin.ext (by simpa [c', d'] using congrArg Fin.val h))
      have hlabc : GGHalfBlk.L.lab c' = c := by ext; simp [GGHalfBlk.lab, GGHalfBlk.off, c']
      have hlabd : GGHalfBlk.L.lab d' = d := by ext; simp [GGHalfBlk.lab, GGHalfBlk.off, d']
      have hframe : m.frame .L c d = m.frame .L (GGHalfBlk.L.lab c') (GGHalfBlk.L.lab d') := by
        rw [hlabc, hlabd]
      rw [hframe, hL c' d' hcd']
      refine Subgroup.subset_closure ⟨slE c' d', ⟨c', d', ?_, ?_, hcd', rfl⟩, rfl⟩
      · show 2 ≤ c'.val; exact hc2
      · show 2 ≤ d'.val; exact hd2
    have hsub1 : φ₁ '' S1 ⊆ Subgroup.closure (φ '' S0) := by
      rintro y ⟨s, hs, rfl⟩
      obtain ⟨c, d, hc, hd, hcd, rfl⟩ := hs
      rw [← hL c d hcd]
      refine Subgroup.subset_closure ⟨ggE6x (m.frame .L (GGHalfBlk.L.lab c) (GGHalfBlk.L.lab d)),
        ⟨GGHalfBlk.L.lab c, GGHalfBlk.L.lab d, ?_, ?_, ?_, ?_, ?_, rfl⟩, rfl⟩
      · show 2 ≤ (GGHalfBlk.L.lab c).val; simpa [GGHalfBlk.lab, GGHalfBlk.off] using hc
      · show (GGHalfBlk.L.lab c).val < 6; simpa [GGHalfBlk.lab, GGHalfBlk.off] using c.isLt
      · show 2 ≤ (GGHalfBlk.L.lab d).val; simpa [GGHalfBlk.lab, GGHalfBlk.off] using hd
      · show (GGHalfBlk.L.lab d).val < 6; simpa [GGHalfBlk.lab, GGHalfBlk.off] using d.isLt
      · intro heq
        exact hcd (Fin.ext (by simpa [GGHalfBlk.lab, GGHalfBlk.off] using congrArg Fin.val heq))
    have hclosure_eq : Subgroup.closure (φ '' S0) = Subgroup.closure (φ₁ '' S1) := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; exact hsub0
      · rw [Subgroup.closure_le]; exact hsub1
    rw [hmapJ0, hJeq]
    exact hclosure_eq

end GGHalfCtx

end CFSG.StandardType

end
