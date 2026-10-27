module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneConj
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcE6Two
public import CFSG.Quasithin.EmptyFaithful.A38c15Gl2
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviPlane
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType.TorC

open CFSG.Open CFSG.StandardType.SpJoin CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {F : Type} [Field F]

structure SpTorusData (F : Type) [Field F] (m p : ℕ) where
  ζm : Multiplicative (ZMod m) →* Matrix.SpecialLinearGroup (Fin 2) F
  ζp : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) F
  inj_m : Function.Injective ζm
  inv_m : ∀ a, sl2W * ζm a * sl2W⁻¹ = ζm a⁻¹
  inj_p : Function.Injective ζp
  mem_m : ∀ a, ∃ b, ζm b = ζp a
  tors : ∀ b, ζm b ^ p = 1 → ∃ a, ζp a = ζm b
  cent : ∀ h : Matrix.SpecialLinearGroup (Fin 2) F,
    h * ζp (Multiplicative.ofAdd 1) = ζp (Multiplicative.ofAdd 1) * h → h ∈ ζm.range
  conj : SpPlaneConj F p ζp

theorem exists_eq_of_pow_eq_one {G : Type*} [Group G] {m p : ℕ} (hm : 0 < m) (hp : p.Prime)
    {ζm : Multiplicative (ZMod m) →* G} (hζm : Function.Injective ζm)
    {ζp : Multiplicative (ZMod p) →* G} (hζp : Function.Injective ζp)
    (hmem : ∀ a, ∃ b, ζm b = ζp a) : ∀ b, ζm b ^ p = 1 → ∃ a, ζp a = ζm b := by
  classical
  have : NeZero m := ⟨hm.ne'⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  choose f hf using hmem
  have hfinj : Function.Injective f := by
    intro a a' h
    apply hζp
    rw [← hf a, ← hf a', h]
  let S : Finset (Multiplicative (ZMod m)) := Finset.univ.filter (fun b => b ^ p = 1)
  have hScard : S.card ≤ p := by
    simpa [S] using
      (IsCyclic.card_pow_eq_one_le (α := Multiplicative (ZMod m)) (n := p) hp.pos)
  have hcardp : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod]
  have hptors : ∀ a : Multiplicative (ZMod p), a ^ p = 1 := by
    intro a
    have h := pow_card_eq_one' (G := Multiplicative (ZMod p)) (x := a)
    rwa [hcardp] at h
  have himage_sub : (Finset.univ.image f) ⊆ S := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    apply hζm
    rw [map_pow, hf, ← map_pow, hptors a, map_one, map_one]
  have himage_card : (Finset.univ.image f).card = p := by
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcardp]
  have hS_eq : (Finset.univ.image f) = S :=
    Finset.eq_of_subset_of_card_le himage_sub (by rw [himage_card]; exact hScard)
  intro b hb
  have hbS : b ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    apply hζm
    rw [map_pow, hb, map_one]
  rw [← hS_eq] at hbS
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hbS
  exact ⟨a, (hf a).symm⟩

theorem nonempty_spTorusData_split [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) : Nonempty (SpTorusData F (Nat.card F - 1) p) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcardF : 1 < Nat.card F := Finite.one_lt_card
  have : NeZero (Nat.card F - 1) := ⟨by omega⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hmpos : 0 < Nat.card F - 1 := by omega
  obtain ⟨g, hg⟩ : ∃ g : Fˣ, orderOf g = Nat.card F - 1 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Fˣ)
    exact ⟨g, by rwa [Nat.card_units] at hg⟩
  have hgp : g ^ (Nat.card F - 1) = 1 := hg ▸ pow_orderOf_eq_one g
  obtain ⟨ω, hωo⟩ : ∃ ω : Fˣ, orderOf ω = p := by
    have : Fact p.Prime := ⟨hp⟩
    refine exists_prime_orderOf_dvd_card p ?_
    rw [Fintype.card_units]
    simpa [Nat.card_eq_fintype_card] using hpq
  have hω1 : ω ^ p = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hinjz : Function.Injective (CFSG.StandardType.TableBSymp.zmodPowHom hgp) := by
    rw [injective_iff_map_eq_one]
    exact fun a ha => (CFSG.StandardType.TableBSymp.zmodPowHom_eq_one_iff hgp hg).mp ha
  have hinjw : Function.Injective (CFSG.StandardType.TableBSymp.zmodPowHom hω1) := by
    rw [injective_iff_map_eq_one]
    exact fun a ha => (CFSG.StandardType.TableBSymp.zmodPowHom_eq_one_iff hω1 hωo).mp ha
  have hdiaginj : Function.Injective (sl2Diag : Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F) := by
    intro a b hab
    refine Units.ext ?_
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      ((x : Matrix (Fin 2) (Fin 2) F)) 0 0) hab
    simpa [coe_sl2Diag] using this
  have hinjm : Function.Injective
      (sl2Diag.comp (CFSG.StandardType.TableBSymp.zmodPowHom hgp)) := hdiaginj.comp hinjz
  have hinjp : Function.Injective
      (sl2Diag.comp (CFSG.StandardType.TableBSymp.zmodPowHom hω1)) := hdiaginj.comp hinjw
  have hsurj : ∀ u : Fˣ, ∃ b, CFSG.StandardType.TableBSymp.zmodPowHom hgp b = u := by
    have hcard : Nat.card (CFSG.StandardType.TableBSymp.zmodPowHom hgp).range = Nat.card Fˣ := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinjz, Subgroup.card_top,
        Nat.card_congr (Multiplicative.toAdd :
          Multiplicative (ZMod (Nat.card F - 1)) ≃ ZMod (Nat.card F - 1)), Nat.card_zmod,
        Nat.card_units]
    have htop : (CFSG.StandardType.TableBSymp.zmodPowHom hgp).range = ⊤ :=
      Subgroup.eq_top_of_card_eq _ hcard
    intro u
    have hu : u ∈ (CFSG.StandardType.TableBSymp.zmodPowHom hgp).range := by rw [htop]; trivial
    exact hu
  have hωne : ω ≠ ω⁻¹ := by
    intro heq
    have h2 : ω ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [heq]
      exact inv_mul_cancel ω
    have hdvd : orderOf ω ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hωo] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact hp.ne_one h
    · exact hp2 h
  refine ⟨{ ζm := sl2Diag.comp (CFSG.StandardType.TableBSymp.zmodPowHom hgp)
            ζp := spPlaneZetaSplit ω hω1
            inj_m := hinjm
            inv_m := ?_
            inj_p := hinjp
            mem_m := ?_
            tors := ?_
            cent := ?_
            conj := ?_ }⟩
  · intro a
    change sl2W * sl2Diag ((CFSG.StandardType.TableBSymp.zmodPowHom hgp) a) * sl2W⁻¹ =
      sl2Diag ((CFSG.StandardType.TableBSymp.zmodPowHom hgp) a⁻¹)
    rw [map_inv, sl2W_mul_sl2Diag]
    group
  · intro a
    change ∃ b, sl2Diag ((CFSG.StandardType.TableBSymp.zmodPowHom hgp) b) =
      sl2Diag ((CFSG.StandardType.TableBSymp.zmodPowHom hω1) a)
    obtain ⟨b, hb⟩ := hsurj ((CFSG.StandardType.TableBSymp.zmodPowHom hω1) a)
    exact ⟨b, by rw [hb]⟩
  · intro b hb
    exact exists_eq_of_pow_eq_one hmpos hp hinjm hinjp (fun a => by
      obtain ⟨b, hb⟩ := hsurj ((CFSG.StandardType.TableBSymp.zmodPowHom hω1) a)
      exact ⟨b, by change sl2Diag _ = sl2Diag _; rw [hb]⟩) b hb
  · intro h hh
    let hM : Matrix (Fin 2) (Fin 2) F := (h : Matrix (Fin 2) (Fin 2) F)
    have hD : spPlaneZetaSplit ω hω1 (Multiplicative.ofAdd 1) = sl2Diag ω := by
      change sl2Diag ((CFSG.StandardType.TableBSymp.zmodPowHom hω1)
        (Multiplicative.ofAdd (1 : ZMod p))) = sl2Diag ω
      rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) from by norm_num,
        CFSG.StandardType.TableBSymp.zmodPowHom_natCast, pow_one]
    have hh' : h * sl2Diag ω = sl2Diag ω * h := by rw [← hD]; exact hh
    have hhM : hM * ((sl2Diag ω : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) =
        ((sl2Diag ω : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * hM := by
      have hcoe := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
        (x : Matrix (Fin 2) (Fin 2) F)) hh'
      simpa [hM, Matrix.SpecialLinearGroup.coe_mul] using hcoe
    have hDns : ∀ c : F, ((sl2Diag ω : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) c := by
      intro c hc
      have h00 := congrFun (congrFun hc 0) 0
      have h11 := congrFun (congrFun hc 1) 1
      simp [Matrix.scalar_apply, coe_sl2Diag] at h00 h11
      refine hωne (Units.ext ?_)
      rw [h00, Units.val_inv_eq_inv_val, h11]
    obtain ⟨a, b, hab⟩ := CFSG.Quasithin.A38c15.exists_eq_add_smul_of_commute hDns hhM
    have h01 : hM 0 1 = 0 := by
      rw [hab]
      simp [Matrix.add_apply, Matrix.smul_apply, coe_sl2Diag]
    have h10 : hM 1 0 = 0 := by
      rw [hab]
      simp [Matrix.add_apply, Matrix.smul_apply, coe_sl2Diag]
    have hdet : hM.det = 1 := Matrix.SpecialLinearGroup.det_coe h
    rw [Matrix.det_fin_two, h01, h10, zero_mul, sub_zero] at hdet
    have h00 : hM 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hdet
      exact zero_ne_one hdet
    have hdiag : h = sl2Diag (Units.mk0 (hM 0 0) h00) := by
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j
      · change hM 0 0 = ((Units.mk0 (hM 0 0) h00 : Fˣ) : F)
        simp
      · change hM 0 1 = 0
        exact h01
      · change hM 1 0 = 0
        exact h10
      · change hM 1 1 = (((Units.mk0 (hM 0 0) h00 : Fˣ) : F))⁻¹
        rw [Units.val_mk0]
        exact eq_inv_of_mul_eq_one_right hdet
    obtain ⟨b, hb⟩ := hsurj (Units.mk0 (hM 0 0) h00)
    refine ⟨b, ?_⟩
    rw [hdiag]
    change sl2Diag ((CFSG.StandardType.TableBSymp.zmodPowHom hgp) b) = sl2Diag _
    rw [hb]
  · have hpF : (p : F) ≠ 0 :=
      natCast_ne_zero_of_two_eq_zero (CharP.cast_eq_zero F 2) hp2 hp
    have : Fact p.Prime := ⟨hp⟩
    exact spPlaneConj_split hp2 hpF hω1 hωo


theorem exists_spTorusData_companion [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {t : F} (hirr : Irreducible (Polynomial.X ^ 2 +
      Polynomial.C t * Polynomial.X + 1 : Polynomial F))
    (hgd : (Polynomial.X ^ 2 + Polynomial.C t * Polynomial.X + 1 : Polynomial F) ∣
      Polynomial.cyclotomic p F) :
    ∃ D : SpTorusData F (Nat.card F + 1) p,
      D.ζp = spPlaneZetaCompanion t (spCompanion_pow_eq_one hp hgd) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero (Nat.card F + 1) := ⟨by omega⟩
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have ht : spCompanion t ^ p = 1 := spCompanion_pow_eq_one hp hgd
  have hconj : SpPlaneConj F p (spPlaneZetaCompanion t ht) :=
    spPlaneConj_companion h2 hp hp2 hpq hirr hgd ht
  have hM1 : spPlaneZetaCompanion t ht (Multiplicative.ofAdd 1) = spCompanion t := by
    change (CFSG.StandardType.TableBSymp.zmodPowHom ht) (Multiplicative.ofAdd (1 : ZMod p)) = _
    rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) from by norm_num,
      CFSG.StandardType.TableBSymp.zmodPowHom_natCast, pow_one]
  have hMne : spCompanion t ≠ 1 := by
    intro h
    have h00 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      ((x : Matrix (Fin 2) (Fin 2) F)) 0 0) h
    rw [coe_spCompanion] at h00
    simp at h00
  have hMo : orderOf (spCompanion t) = p := by
    have hdvd : orderOf (spCompanion t) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr ht
    rcases (Nat.dvd_prime hp).mp hdvd with h | h
    · rw [orderOf_eq_one_iff] at h
      exact absurd h hMne
    · exact h
  have hinjp : Function.Injective (spPlaneZetaCompanion t ht) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact (CFSG.StandardType.TableBSymp.zmodPowHom_eq_one_iff ht hMo).mp ha
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := F)
  have hAp : A ^ (Nat.card F + 1) = 1 := hA ▸ pow_orderOf_eq_one A
  have hqpos : 0 < (Nat.card F + 1) / p :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hpq) hp.pos
  have hmul : Nat.card F + 1 = p * ((Nat.card F + 1) / p) := (Nat.mul_div_cancel' hpq).symm
  have hkp : ((Nat.card F + 1) / p) * p = Nat.card F + 1 := by
    rw [Nat.mul_comm, Nat.mul_div_cancel' hpq]
  have hdiv : (Nat.card F + 1) / ((Nat.card F + 1) / p) = p := by
    nth_rewrite 1 [hmul]
    rw [Nat.mul_comm p ((Nat.card F + 1) / p), Nat.mul_div_right p hqpos]
  have hdk : ((Nat.card F + 1) / p) ∣ orderOf A := by
    rw [hA]
    exact ⟨p, hkp.symm⟩
  have hS'pow : (A ^ ((Nat.card F + 1) / p)) ^ p = 1 := by
    rw [← pow_mul, hkp, hAp]
  have hS'o : orderOf (A ^ ((Nat.card F + 1) / p)) = p := by
    rw [orderOf_pow_of_dvd hqpos.ne' hdk, hA, hdiv]
  let S' : Matrix.SpecialLinearGroup (Fin 2) F := A ^ ((Nat.card F + 1) / p)
  let L : Matrix.SpecialLinearGroup (Fin 2) F →* StatedSp 1 F := lam (0 : Fin 1)
  let E : Subgroup (StatedSp 1 F) := Subgroup.zpowers (L S')
  have hEcard : Nat.card E = p := by
    rw [show Nat.card E = orderOf (L S') from Nat.card_zpowers (L S'),
      orderOf_injective L (lam_injective 0) S', hS'o]
  have hE : IsElemAbelian p E := by
    refine ⟨?_, ?_⟩
    · have : IsCyclic E := Subgroup.isCyclic_zpowers (L S')
      infer_instance
    · intro x hx
      have h := pow_card_eq_one' (G := ↥E) (x := (⟨x, hx⟩ : ↥E))
      rw [hEcard] at h
      simpa using congrArg (fun y : ↥E => (y : StatedSp 1 F)) h
  have hcardE : p ^ 1 ≤ Nat.card E := by rw [pow_one, hEcard]
  obtain ⟨c, hc⟩ := hconj 1 E hE hcardE
  obtain ⟨γ, hγ⟩ := lam_zero_surjective c
  have hmem_range : L (γ * S' * γ⁻¹) ∈ (spPlaneTorus 1 (spPlaneZetaCompanion t ht)).range := by
    rw [← hc, Subgroup.mem_map]
    refine ⟨L S', Subgroup.mem_zpowers _, ?_⟩
    show c * L S' * c⁻¹ = L (γ * S' * γ⁻¹)
    rw [← hγ, map_mul, map_mul, map_inv]
  obtain ⟨f, hf⟩ := hmem_range
  have hf0 : f = Pi.mulSingle (0 : Fin 1) (f 0) := by
    funext i
    fin_cases i
    simp
  rw [hf0, spPlaneTorus_mulSingle] at hf
  have ha₀ : spPlaneZetaCompanion t ht (f 0) = γ * S' * γ⁻¹ := lam_injective 0 hf
  have hconj_o : orderOf (γ * S' * γ⁻¹) = p := by
    rw [show γ * S' * γ⁻¹ = (MulAut.conj γ).toMonoidHom S' from rfl,
      orderOf_injective (MulAut.conj γ).toMonoidHom (MulEquiv.injective _) S', hS'o]
  have ha₀ne : f 0 ≠ 1 := by
    intro h1
    have h2 : γ * S' * γ⁻¹ = 1 := by rw [← ha₀, h1, map_one]
    rw [h2, orderOf_one] at hconj_o
    exact (Nat.Prime.one_lt hp).ne' hconj_o.symm
  have hpow : spPlaneZetaCompanion t ht (f 0) =
      (spCompanion t) ^ (Multiplicative.toAdd (f 0)).val := by
    change (CFSG.StandardType.TableBSymp.zmodPowHom ht) (f 0) = _
    exact CFSG.StandardType.TableBSymp.zmodPowHom_apply ht (f 0)
  let ζm : Multiplicative (ZMod (Nat.card F + 1)) →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MulAut.conj γ).toMonoidHom.comp (CFSG.StandardType.TableBSymp.zmodPowHom hAp)
  have hinjz : Function.Injective (CFSG.StandardType.TableBSymp.zmodPowHom hAp) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact (CFSG.StandardType.TableBSymp.zmodPowHom_eq_one_iff hAp hA).mp ha
  have hinj_m : Function.Injective ζm := by
    intro a b hab
    exact hinjz ((MulEquiv.injective (MulAut.conj γ)) hab)
  have hzrange : (CFSG.StandardType.TableBSymp.zmodPowHom hAp).range = Subgroup.zpowers A := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨n, rfl⟩
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨(Multiplicative.toAdd n).val,
        by rw [zpow_natCast, CFSG.StandardType.TableBSymp.zmodPowHom_apply]⟩
    · rw [Nat.card_zpowers, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinjz,
        Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd :
          Multiplicative (ZMod (Nat.card F + 1)) ≃ ZMod (Nat.card F + 1)), Nat.card_zmod, hA]
  have hmapζm : ζm.range = (Subgroup.zpowers A).map (MulAut.conj γ).toMonoidHom := by
    rw [show ζm = (MulAut.conj γ).toMonoidHom.comp
        (CFSG.StandardType.TableBSymp.zmodPowHom hAp) from rfl, ← MonoidHom.map_range, hzrange]
  have hzp_eq : Subgroup.zpowers (γ * S' * γ⁻¹) = (spPlaneZetaCompanion t ht).range := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.zpowers_le, ← ha₀]
      exact MonoidHom.mem_range.mpr ⟨f 0, rfl⟩
    · rw [Nat.card_zpowers, hconj_o, MonoidHom.range_eq_map,
        Subgroup.card_map_of_injective hinjp, Subgroup.card_top,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod]
  have hsub : (spPlaneZetaCompanion t ht).range ≤ ζm.range := by
    rw [← hzp_eq, hmapζm, Subgroup.zpowers_le, Subgroup.mem_map]
    refine ⟨S', ?_, rfl⟩
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨(((Nat.card F + 1) / p : ℕ) : ℤ), by rw [zpow_natCast]⟩
  have hmem_m : ∀ a, ∃ b, ζm b = spPlaneZetaCompanion t ht a := fun a =>
    MonoidHom.mem_range.mp (hsub (MonoidHom.mem_range.mpr ⟨a, rfl⟩))
  have hinv_m : ∀ b, sl2W * ζm b * sl2W⁻¹ = ζm b⁻¹ := by
    intro b
    have hneg : (-1 : F) = 1 := by
      rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two]
      exact h2
    have htneg : -t = t := by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
    have hW2 : (sl2W : Matrix.SpecialLinearGroup (Fin 2) F) * sl2W = 1 := by
      rw [sl2W_mul_sl2W]
      apply Matrix.SpecialLinearGroup.ext
      rw [Matrix.SpecialLinearGroup.coe_one, coe_sl2Diag]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [hneg]
    have hWeq : (sl2W : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ = sl2W :=
      inv_eq_of_mul_eq_one_right hW2
    have hMmem : spCompanion t ∈ ζm.range := by
      obtain ⟨b', hb'⟩ := hmem_m (Multiplicative.ofAdd (1 : ZMod p))
      exact ⟨b', by rw [hb', hM1]⟩
    have hxM : ((ζm b : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *
        ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((ζm b : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      obtain ⟨b', hb'⟩ := hMmem
      have hcomm : (ζm b : Matrix.SpecialLinearGroup (Fin 2) F) * spCompanion t =
          spCompanion t * ζm b := by
        rw [← hb', ← map_mul, ← map_mul, mul_comm b b']
      exact congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
        (x : Matrix (Fin 2) (Fin 2) F)) hcomm
    have hMns : ∀ c : F, ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) c := by
      intro c hcs
      have h01 := congrFun (congrFun hcs 0) 1
      rw [coe_spCompanion] at h01
      simp [Matrix.scalar_apply] at h01
    obtain ⟨α, β, hαβ⟩ := CFSG.Quasithin.A38c15.exists_eq_add_smul_of_commute hMns hxM
    have hMinv : (((spCompanion t)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = !![t, 1; 1, 0] := by
      rw [Matrix.SpecialLinearGroup.coe_inv, coe_spCompanion, Matrix.adjugate_fin_two_of]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hneg, htneg]
    have hwM : ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *
        ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (((spCompanion t)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := by
      have hcoe := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
        (x : Matrix (Fin 2) (Fin 2) F)) (sl2W_conj_spCompanion h2 t)
      rw [hWeq] at hcoe
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using hcoe
    have hadj : (α • (1 : Matrix (Fin 2) (Fin 2) F) +
          β • ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)).adjugate =
        α • (1 : Matrix (Fin 2) (Fin 2) F) +
          β • ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F).adjugate := by
      rw [Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.add_apply, Matrix.smul_apply]
    have hgoal : ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) *
        (α • (1 : Matrix (Fin 2) (Fin 2) F) +
          β • ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)) *
        ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        α • (1 : Matrix (Fin 2) (Fin 2) F) + β • !![t, 1; 1, 0] := by
      have hw1 : ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) * (1 : Matrix (Fin 2) (Fin 2) F) *
          ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
        rw [mul_one, ← Matrix.SpecialLinearGroup.coe_mul, hW2, Matrix.SpecialLinearGroup.coe_one]
      have hwM' : ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) *
          ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          !![t, 1; 1, 0] := by
        rw [hwM, hMinv]
      calc ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) *
          (α • (1 : Matrix (Fin 2) (Fin 2) F) +
            β • ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F)) *
          ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = α • (((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) * (1 : Matrix (Fin 2) (Fin 2) F) *
              ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) +
            β • (((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) *
              ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) *
              ((sl2W : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) := by
            simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
        _ = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • !![t, 1; 1, 0] := by rw [hw1, hwM']
    rw [hWeq]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, map_inv,
      Matrix.SpecialLinearGroup.coe_inv, hαβ]
    have hMinv2 : ((spCompanion t : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).adjugate = !![t, 1; 1, 0] := by
      rw [coe_spCompanion, Matrix.adjugate_fin_two_of]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hneg, htneg]
    rw [hadj, hMinv2]
    exact hgoal
  have hcent : ∀ h : Matrix.SpecialLinearGroup (Fin 2) F,
      h * spPlaneZetaCompanion t ht (Multiplicative.ofAdd 1) =
        spPlaneZetaCompanion t ht (Multiplicative.ofAdd 1) * h → h ∈ ζm.range := by
    intro h hh
    have hcommM : Commute h (spCompanion t) := by
      show h * spCompanion t = spCompanion t * h
      rw [← hM1]
      exact hh
    have hhS : h * (γ * S' * γ⁻¹) = (γ * S' * γ⁻¹) * h := by
      rw [← ha₀, hpow]
      exact (hcommM.pow_right (Multiplicative.toAdd (f 0)).val).eq
    have hh1 : (γ⁻¹ * h * γ) * S' = S' * (γ⁻¹ * h * γ) := by
      have hconj := congrArg (fun x => γ⁻¹ * x * γ) hhS
      simpa [mul_assoc] using hconj
    have hXcyc : IsCyclic ↥(Subgroup.zpowers A) := Subgroup.isCyclic_zpowers A
    have hXcard : Nat.card ↥(Subgroup.zpowers A) = Nat.card F + 1 := by
      rw [Nat.card_zpowers, hA]
    have hS'X : S' ∈ Subgroup.zpowers A := by
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨(((Nat.card F + 1) / p : ℕ) : ℤ), by rw [zpow_natCast]⟩
    have hcent_eq : Subgroup.centralizer ({S'} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) =
        Subgroup.zpowers A := by
      have : Fact p.Prime := ⟨hp⟩
      exact CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two.centralizer_sl2_eq_of_isCyclic_of_mem
        (K := F) hp2 hpq hXcyc hXcard hS'X hS'o
    have hmem : γ⁻¹ * h * γ ∈ Subgroup.zpowers A := by
      rw [← hcent_eq]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hh1
    rw [hmapζm, Subgroup.mem_map]
    exact ⟨γ⁻¹ * h * γ, hmem, by simp [MulAut.conj_apply, mul_assoc]⟩
  have htors : ∀ b, ζm b ^ p = 1 → ∃ a, spPlaneZetaCompanion t ht a = ζm b :=
    exists_eq_of_pow_eq_one (Nat.succ_pos _) hp hinj_m hinjp hmem_m
  exact ⟨{ ζm := ζm
           ζp := spPlaneZetaCompanion t ht
           inj_m := hinj_m
           inv_m := hinv_m
           inj_p := hinjp
           mem_m := hmem_m
           tors := htors
           cent := hcent
           conj := hconj }, rfl⟩

theorem nonempty_spTorusData_nonsplit [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) : Nonempty (SpTorusData F (Nat.card F + 1) p) := by
  have hpF : (p : F) ≠ 0 :=
    natCast_ne_zero_of_two_eq_zero (CharP.cast_eq_zero F 2) hp2 hp
  obtain ⟨t, hirr, hgd⟩ := exists_quadratic_cyclotomic_factor hp hp2 hpF hpq
  obtain ⟨D, -⟩ := exists_spTorusData_companion hp hp2 hpq hirr hgd
  exact ⟨D⟩

end CFSG.StandardType.TorC

end
