module

public import CFSG.Quasithin.Background.FFC4Zmod
public import CFSG.Quasithin.Background.FFC4Real

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank Equiv Equiv.Perm

section Five

theorem allOnes_zpow_five (k : ℤ) :
    G6.allOnes 5 ^ k = Multiplicative.ofAdd (fun _ : Fin 5 => (k : ZMod 2)) := by
  rw [G6.allOnes, ← ofAdd_zsmul]
  congr 1
  funext i
  simp

theorem natKer_five : Subgroup.zpowers (G6.allOnes 5) ⊓ G6.coreMod 5 = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx1
  rw [allOnes_zpow_five] at hx2 ⊢
  have h1 : (∑ _i : Fin 5, (k : ZMod 2)) = 0 := hx2
  have h2 : (k : ZMod 2) = 0 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have h5 : ((5 : ℕ) : ZMod 2) = 1 := by decide
    rwa [h5, one_mul] at h1
  rw [h2]
  exact Subgroup.one_mem _

theorem symDn_ker_five : (FFModel.symDn 5).ker = ⊥ := natKer_five

theorem altDn_ker_five : (FFModel.altDn 5).ker = ⊥ := natKer_five

theorem card_coreMod_five : Nat.card ↥(G6.coreMod 5) = 16 := by
  have h : Nat.card ↥(G6.coreMod 5) = Nat.card {f : Fin 5 → ZMod 2 // ∑ i, f i = 0} :=
    Nat.card_congr
      { toFun := fun x => ⟨Multiplicative.toAdd x.1, x.2⟩
        invFun := fun f => ⟨Multiplicative.ofAdd f.1, f.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h, Nat.card_eq_fintype_card]
  decide +kernel

theorem card_fix_one_le : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ * σ = 1 → sign σ = 1 →
    (Finset.univ.filter (fun m : Fin 5 → ZMod 2 => ∑ i, m i = 0 ∧ ∀ i, m (σ⁻¹ i) = m i)).card ≤ 4 := by
  decide +kernel

theorem card_fix_two_le : ∀ σ τ : Perm (Fin 5), σ ≠ 1 → τ ≠ 1 → σ ≠ τ → σ * σ = 1 → τ * τ = 1 →
    σ * τ = τ * σ → sign σ = 1 → sign τ = 1 →
    (Finset.univ.filter (fun m : Fin 5 → ZMod 2 => ∑ i, m i = 0 ∧ (∀ i, m (σ⁻¹ i) = m i) ∧
      ∀ i, m (τ⁻¹ i) = m i)).card ≤ 2 := by
  decide +kernel

theorem exists_fix_three : ∀ σ : Perm (Fin 5), σ ^ 3 = 1 → σ ≠ 1 →
    ∃ m : Fin 5 → ZMod 2, ∑ i, m i = 0 ∧ m ≠ 0 ∧ ∀ i, m (σ⁻¹ i) = m i := by
  decide +kernel

@[expose] noncomputable def fixS (σ : Perm (Fin 5)) : Finset (G6.PermMod 5) :=
  (Finset.univ.filter (fun m : Fin 5 → ZMod 2 => ∑ i, m i = 0 ∧ ∀ i, m (σ⁻¹ i) = m i)).image
    Multiplicative.ofAdd

theorem mem_fixS {σ : Perm (Fin 5)} {y : G6.PermMod 5} (hy : y ∈ G6.coreMod 5)
    (hfix : G6.permAct 5 σ y = y) : y ∈ fixS σ := by
  refine Finset.mem_image.2 ⟨Multiplicative.toAdd y, ?_, ofAdd_toAdd y⟩
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hy, fun i => ?_⟩
  have := congrArg (fun z : G6.PermMod 5 => Multiplicative.toAdd z i) hfix
  simpa [G6.permAct_apply] using this

@[expose] noncomputable def fixS₂ (σ τ : Perm (Fin 5)) : Finset (G6.PermMod 5) :=
  (Finset.univ.filter (fun m : Fin 5 → ZMod 2 => ∑ i, m i = 0 ∧ (∀ i, m (σ⁻¹ i) = m i) ∧
    ∀ i, m (τ⁻¹ i) = m i)).image Multiplicative.ofAdd

theorem mem_fixS₂ {σ τ : Perm (Fin 5)} {y : G6.PermMod 5} (hy : y ∈ G6.coreMod 5)
    (hσ : G6.permAct 5 σ y = y) (hτ : G6.permAct 5 τ y = y) : y ∈ fixS₂ σ τ := by
  refine Finset.mem_image.2 ⟨Multiplicative.toAdd y, ?_, ofAdd_toAdd y⟩
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, hy, fun i => ?_, fun i => ?_⟩
  · have := congrArg (fun z : G6.PermMod 5 => Multiplicative.toAdd z i) hσ
    simpa [G6.permAct_apply] using this
  · have := congrArg (fun z : G6.PermMod 5 => Multiplicative.toAdd z i) hτ
    simpa [G6.permAct_apply] using this

theorem card_fixS_le {σ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : σ * σ = 1) (h3 : sign σ = 1) :
    (fixS σ).card ≤ 4 :=
  Finset.card_image_le.trans (card_fix_one_le σ h1 h2 h3)

theorem card_fixS₂_le {σ τ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : τ ≠ 1) (h3 : σ ≠ τ) (h4 : σ * σ = 1)
    (h5 : τ * τ = 1) (h6 : σ * τ = τ * σ) (h7 : sign σ = 1) (h8 : sign τ = 1) :
    (fixS₂ σ τ).card ≤ 2 :=
  Finset.card_image_le.trans (card_fix_two_le σ τ h1 h2 h3 h4 h5 h6 h7 h8)

end Five

section Model

variable {W : Type*} [CommGroup W]

theorem exists_modelHom {D : FFModel} (hker : D.ker = ⊥) {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (hα : U ⊔ fixV H = ⊤) (hUZ : U ⊓ fixV H = Z) :
    ∃ q : W →* D.Amb, (∀ w, q w ∈ D.sec) ∧ (∀ m ∈ D.sec, ∃ w, q w = m) ∧
      (∀ w, q w = 1 ↔ w ∈ fixV H) ∧
      ∀ (γ : D.Gam) (w : W), q (((π γ : ↥H) : MulAut W) w) = D.act γ (q w) := by
  have hCinv : ∀ g : ↥H, ∀ c ∈ fixV H, (g : MulAut W) c ∈ fixV H := fun g c hc => by
    rw [hc g g.2]; exact hc
  have hext := RealizesVia.extend h hCinv hUZ
  rw [hα] at hext
  obtain ⟨f, hfs, hfk, hfe⟩ := RealizesVia.secMap hker hext
  let q : W →* D.Amb :=
    { toFun := fun w => ((f ⟨w, Subgroup.mem_top w⟩ : ↥D.sec) : D.Amb)
      map_one' := by
        have h1 : (⟨1, Subgroup.mem_top 1⟩ : ↥(⊤ : Subgroup W)) = 1 := rfl
        show ((f ⟨1, Subgroup.mem_top 1⟩ : ↥D.sec) : D.Amb) = 1
        rw [h1, map_one]
        rfl
      map_mul' := fun a b => by
        have h1 : (⟨a * b, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
            ⟨a, Subgroup.mem_top _⟩ * ⟨b, Subgroup.mem_top _⟩ := rfl
        show ((f ⟨a * b, Subgroup.mem_top _⟩ : ↥D.sec) : D.Amb) =
          ((f ⟨a, Subgroup.mem_top _⟩ : ↥D.sec) : D.Amb) * ((f ⟨b, Subgroup.mem_top _⟩ : ↥D.sec) : D.Amb)
        rw [h1, map_mul]
        rfl }
  refine ⟨q, fun w => (f _).2, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨u, hu⟩ := hfs ⟨m, hm⟩
    refine ⟨(u : W), ?_⟩
    have : (⟨(u : W), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) = u := rfl
    show ((f ⟨(u : W), Subgroup.mem_top _⟩ : ↥D.sec) : D.Amb) = m
    rw [this, hu]
  · intro w
    rw [← hfk ⟨w, Subgroup.mem_top w⟩]
    constructor
    · intro h1
      exact Subtype.ext h1
    · intro h1
      exact congrArg Subtype.val h1
  · intro γ w
    exact hfe γ ⟨w, Subgroup.mem_top w⟩ trivial

theorem card_le_of_maps_into {G P : Type*} [Group G] [Finite G] [Group P] (q : G →* P)
    (K : Subgroup G) (S : Finset P) (hS : ∀ k ∈ K, q k ∈ S) :
    Nat.card K ≤ Nat.card q.ker * S.card := by
  classical
  let ψ : ↥K →* P := q.comp K.subtype
  have h1 : Nat.card ψ.ker * Nat.card ψ.range = Nat.card K := Subgroup.card_ker_mul_card_range ψ
  have h2 : Nat.card ψ.ker ≤ Nat.card q.ker := by
    refine Nat.card_le_card_of_injective (fun x => (⟨(x.1 : G), x.2⟩ : ↥q.ker)) ?_
    intro x y hxy
    have h' : ((x.1 : ↥K) : G) = ((y.1 : ↥K) : G) := congrArg (fun z : ↥q.ker => (z : G)) hxy
    exact Subtype.ext (Subtype.ext h')
  have h3 : Nat.card ψ.range ≤ S.card := by
    have h4 : Nat.card ψ.range ≤ Nat.card (S : Set P) := by
      refine Nat.card_le_card_of_injective (fun x => (⟨x.1, ?_⟩ : ↥(S : Set P))) ?_
      · obtain ⟨k, hk⟩ := x.2
        rw [← hk]
        exact hS k k.2
      · intro x y hxy
        have h' : (x.1 : P) = (y.1 : P) := congrArg (fun z : ↥(S : Set P) => (z : P)) hxy
        exact Subtype.ext h'
    simpa using h4
  calc Nat.card K = Nat.card ψ.ker * Nat.card ψ.range := h1.symm
    _ ≤ Nat.card q.ker * S.card := Nat.mul_le_mul h2 h3

theorem card_eq_of_realizes {D : FFModel} (hker : D.ker = ⊥) {H : Subgroup (MulAut W)}
    {U Z : Subgroup W} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    Nat.card U = Nat.card Z * Nat.card D.sec := by
  obtain ⟨f, hfs, hfk, -⟩ := RealizesVia.secMap hker h
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.ker = Nat.card Z :=
    Nat.card_congr
      { toFun := fun x => ⟨(x.1 : W), (hfk x.1).1 x.2⟩
        invFun := fun z => ⟨⟨z.1, h.2.1 z.2⟩, (hfk _).2 z.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h3 : Nat.card f.range = Nat.card D.sec := by
    rw [f.range_eq_top_of_surjective hfs, Subgroup.card_top]
  rw [← h1, h2, h3]

end Model

section Alt5

variable {W : Type} [CommGroup W]

theorem card_alt_five : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem lift_props {H : Subgroup (MulAut W)} {π : ↥(alternatingGroup (Fin 5)) →* ↥H}
    (hinj : Function.Injective π) {a : MulAut W} (σ : ↥(alternatingGroup (Fin 5)))
    (hσ : ((π σ : ↥H) : MulAut W) = a) (h1 : a ≠ 1) (h2 : a ^ 2 = 1) :
    (σ : Perm (Fin 5)) ≠ 1 ∧ (σ : Perm (Fin 5)) * σ = 1 ∧ sign (σ : Perm (Fin 5)) = 1 := by
  refine ⟨fun h => ?_, ?_, Equiv.Perm.mem_alternatingGroup.1 σ.2⟩
  · have h' : σ = 1 := Subtype.ext h
    rw [h', map_one] at hσ
    exact h1 hσ.symm
  · have h3 : π (σ * σ) = 1 := by
      apply Subtype.ext
      rw [map_mul]
      show ((π σ : ↥H) : MulAut W) * ((π σ : ↥H) : MulAut W) = 1
      rw [hσ, ← pow_two]
      exact h2
    have h4 : σ * σ = 1 := hinj (h3.trans (map_one π).symm)
    exact congrArg Subtype.val h4

theorem lift_pair {H : Subgroup (MulAut W)} {π : ↥(alternatingGroup (Fin 5)) →* ↥H}
    (hinj : Function.Injective π) {a b : MulAut W} (σ τ : ↥(alternatingGroup (Fin 5)))
    (hσ : ((π σ : ↥H) : MulAut W) = a) (hτ : ((π τ : ↥H) : MulAut W) = b) (hab : a ≠ b)
    (hc : a * b = b * a) :
    (σ : Perm (Fin 5)) ≠ τ ∧ (σ : Perm (Fin 5)) * τ = τ * σ := by
  refine ⟨fun h => ?_, ?_⟩
  · have h' : σ = τ := Subtype.ext h
    rw [h'] at hσ
    exact hab (hσ.symm.trans hτ)
  · have h3 : π (σ * τ) = π (τ * σ) := by
      apply Subtype.ext
      rw [map_mul, map_mul]
      show ((π σ : ↥H) : MulAut W) * ((π τ : ↥H) : MulAut W) =
        ((π τ : ↥H) : MulAut W) * ((π σ : ↥H) : MulAut W)
      rw [hσ, hτ]
      exact hc
    exact congrArg Subtype.val (hinj h3)

theorem false_of_alt5 [Finite W] {H : Subgroup (MulAut W)} {U Z : Subgroup W} (hJ : H = ffJ H)
    (hne : H ≠ ⊥) (hα : U ⊔ fixV H = ⊤) (hUZ : U ⊓ fixV H = Z) (h : AlternatingNatural H U Z 5) :
    False := by
  obtain ⟨π, hπ⟩ := h
  have hinj : Function.Injective π := injective_of_faithful_sec (altDn_faithful (by norm_num)) hπ
  have hπs : Function.Surjective π := hπ.1
  obtain ⟨q, hqs, hqr, hqk, hqe⟩ := exists_modelHom altDn_ker_five hπ hα hUZ
  have hker : q.ker = fixV H := by
    ext w
    exact hqk w
  have hrange : q.range = G6.coreMod 5 := by
    ext m
    constructor
    · rintro ⟨w, rfl⟩
      exact hqs w
    · intro hm
      obtain ⟨w, hw⟩ := hqr m hm
      exact ⟨w, hw⟩
  have hc : 0 < Nat.card ↥(fixV H) := Nat.card_pos
  have hW : Nat.card W = 16 * Nat.card ↥(fixV H) := by
    have h1 := Subgroup.card_ker_mul_card_range q
    have h2 : Nat.card q.range = 16 :=
      (congrArg (fun S : Subgroup (G6.PermMod 5) => Nat.card S) hrange).trans card_coreMod_five
    rw [hker, h2] at h1
    rw [← h1]
    ring
  obtain ⟨A, hA⟩ : ∃ A, IsFFStarOffender H A := by
    by_contra hcon
    push Not at hcon
    have h0 : ffJ H = ⊥ := by
      unfold ffJ
      exact iSup_eq_bot.2 fun A => iSup_eq_bot.2 fun hA => absurd hA (hcon A)
    exact hne (hJ.trans h0)
  obtain ⟨hAH, hA1, ⟨hcomm, hsq⟩, hoff⟩ := hA
  have hlift : ∀ a ∈ A, ∃ σ : ↥(alternatingGroup (Fin 5)), ((π σ : ↥H) : MulAut W) = a := by
    intro a ha
    obtain ⟨σ, hσ⟩ := hπs ⟨a, hAH ha⟩
    exact ⟨σ, congrArg Subtype.val hσ⟩
  have hbot := hoff ⊥ bot_le
  rw [B1.fixV_bot, Subgroup.card_bot, Subgroup.card_top, one_mul] at hbot
  have hA4 : Nat.card A ≤ 4 := by
    have hpg : IsPGroup 2 ↥A := fun g => ⟨1, Subtype.ext (by simpa using hsq g g.2)⟩
    obtain ⟨m, hm⟩ := hpg.exists_card_eq
    have hH60 : Nat.card ↥H = 60 := by
      rw [← card_alt_five]
      exact (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπs⟩)).symm
    have hdvd : 2 ^ m ∣ 60 := by
      rw [← hm, ← hH60]
      exact Subgroup.card_dvd_of_le hAH
    have hm2 : m ≤ 2 := by
      by_contra hm3
      have : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 (by omega)).trans hdvd
      norm_num at this
    rw [hm]
    calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 4 := by norm_num
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA1
  have hx1' : (x : MulAut W) ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨σ, hσ⟩ := hlift (x : MulAut W) x.2
  obtain ⟨hσ1, hσ2, hσs⟩ := lift_props hinj σ hσ hx1' (hsq x x.2)
  have hS1 : ∀ k ∈ fixV A, q k ∈ fixS (σ : Perm (Fin 5)) := by
    intro k hk
    have hxk : ((π σ : ↥H) : MulAut W) k = k := by
      rw [hσ]
      exact hk _ x.2
    refine mem_fixS (hqs k) ?_
    have h1 := hqe σ k
    rw [hxk] at h1
    exact h1.symm
  have hfix1 : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV H) * 4 := by
    have h1 := card_le_of_maps_into q (fixV A) (fixS (σ : Perm (Fin 5))) hS1
    rw [hker] at h1
    exact h1.trans (Nat.mul_le_mul_left _ (card_fixS_le hσ1 hσ2 hσs))
  have hA4' : 4 ≤ Nat.card A := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card A * Nat.card ↥(fixV A) ≤ 3 * (Nat.card ↥(fixV H) * 4) :=
      Nat.mul_le_mul (by omega) hfix1
    omega
  have hnle : ¬ A ≤ Subgroup.zpowers (x : MulAut W) := by
    intro hle
    have h1 : Nat.card A ≤ Nat.card (Subgroup.zpowers (x : MulAut W)) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf (x : MulAut W) ≤ 2 :=
      Nat.le_of_dvd two_pos (orderOf_dvd_of_pow_eq_one (hsq x x.2))
    omega
  obtain ⟨y, hyA, hy⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hy1 : y ≠ 1 := fun h => hy (h ▸ Subgroup.one_mem _)
  have hyx : (x : MulAut W) ≠ y := fun h => hy (h ▸ Subgroup.mem_zpowers _)
  obtain ⟨τ, hτ⟩ := hlift y hyA
  obtain ⟨hτ1, hτ2, hτs⟩ := lift_props hinj τ hτ hy1 (hsq y hyA)
  obtain ⟨hστ, hcommτ⟩ := lift_pair hinj σ τ hσ hτ hyx (hcomm x x.2 y hyA)
  have hS2 : ∀ k ∈ fixV A, q k ∈ fixS₂ (σ : Perm (Fin 5)) (τ : Perm (Fin 5)) := by
    intro k hk
    have hxk : ((π σ : ↥H) : MulAut W) k = k := by
      rw [hσ]
      exact hk _ x.2
    have hyk : ((π τ : ↥H) : MulAut W) k = k := by
      rw [hτ]
      exact hk _ hyA
    refine mem_fixS₂ (hqs k) ?_ ?_
    · have h1 := hqe σ k
      rw [hxk] at h1
      exact h1.symm
    · have h1 := hqe τ k
      rw [hyk] at h1
      exact h1.symm
  have hfix2 : Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV H) * 2 := by
    have h1 := card_le_of_maps_into q (fixV A) (fixS₂ (σ : Perm (Fin 5)) (τ : Perm (Fin 5))) hS2
    rw [hker] at h1
    exact h1.trans (Nat.mul_le_mul_left _
      (card_fixS₂_le hσ1 hτ1 hστ hσ2 hτ2 hcommτ hσs hτs))
  have h1 : Nat.card A * Nat.card ↥(fixV A) ≤ 4 * (Nat.card ↥(fixV H) * 2) :=
    Nat.mul_le_mul hA4 hfix2
  omega

end Alt5

end FFC

end CFSG.Quasithin
