module

public import CFSG.LocalAnalysis.StandardType.GGTBTorItems

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTD_span_top {p : ℕ} [Fact p.Prime] {E : Type} [Group E] [Finite E] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) {κ : Type} [Fintype κ]
    (v : κ → V) (hv : LinearIndependent (ZMod p) v) (hcard : Nat.card E ≤ p ^ Fintype.card κ) :
    Submodule.span (ZMod p) (Set.range v) = ⊤ := by
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hV : Nat.card V = Nat.card E :=
    (Nat.card_congr ι.toEquiv).symm.trans (Nat.card_congr Additive.toMul)
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod] at hV
  have h1 := hv.fintype_card_le_finrank
  have h2 : Module.finrank (ZMod p) V ≤ Fintype.card κ :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (hV ▸ hcard)
  exact hv.span_eq_top_of_card_eq_finrank' (le_antisymm h1 h2)

theorem ggTD_sum_eq {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (ι : Additive E ≃+ V) {N : ℕ} (b : Fin N → E)
    (c : Fin N → ZMod p) :
    ∑ i, c i • ι (Additive.ofMul (b i)) =
      ι (Additive.ofMul (List.ofFn fun k => b k ^ (c k).val).prod) := by
  rw [ofMul_list_prod (List.ofFn fun k => b k ^ (c k).val), map_list_sum ι, List.map_map,
    List.map_ofFn, List.sum_ofFn]
  refine Fintype.sum_congr _ _ fun i => ?_
  simp only [Function.comp_apply, ofMul_pow, map_nsmul]
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

theorem ggTD_zeta_val_inj {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0) (hpm : p ∣ m) (u v : ZMod p)
    (h : ggZetaP p m ^ u.val = ggZetaP p m ^ v.val) : u = v := by
  rw [pow_eq_pow_iff_modEq, ggZetaP_orderOf (Fact.out : p.Prime) hm hpm] at h
  rw [← ZMod.natCast_zmod_val u, ← ZMod.natCast_zmod_val v]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h

noncomputable def ggTDρB {G : Type} [Group G] (X Bs : Subgroup G) :
    ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) →* MulAut ↥Bs :=
  Bs.normalizerMonoidHom.comp (Subgroup.inclusion inf_le_right)

theorem ggTDρB_apply {G : Type} [Group G] {Bs X : Subgroup G}
    (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (b : ↥Bs) :
    ((ggTDρB X Bs g b : ↥Bs) : G) = (g : G) * b * (g : G)⁻¹ := rfl

noncomputable def ggTDρA {G : Type} [Group G] {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) :
    ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) →* MulAut ↥(ggGamma X hN).range :=
  (ggGamma X hN).range.normalizerMonoidHom.comp
    (((MulAut.conj : ↥X →* MulAut ↥X).comp (Subgroup.inclusion inf_le_left)).codRestrict _
      fun g => conj_mem_normalizer_range_ggGamma hN g.2.1 g.2.2)

theorem ggTDρA_apply {G : Type} [Group G] {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (a : ↥(ggGamma X hN).range) :
    ((ggTDρA hN g a : ↥(ggGamma X hN).range) : MulAut ↥X) =
      MulAut.conj (⟨g, g.2.1⟩ : ↥X) * a * (MulAut.conj (⟨g, g.2.1⟩ : ↥X))⁻¹ := rfl

theorem ggTD_elemAb {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hBs : IsElemAbelian p Bs) :
    IsElemAbelian p (ggGamma X hN).range := by
  have := hBs.1
  refine ⟨inferInstance, ?_⟩
  rintro _ ⟨b, rfl⟩
  rw [← map_pow]
  have : b ^ p = 1 := Subtype.ext (by simpa using hBs.2 b b.2)
  rw [this, map_one]

theorem ggTDρB_range {G : Type} [Group G] {Bs X : Subgroup G} :
    (ggTDρB X Bs).range = ggAutomizer X Bs := by
  ext φ
  rw [mem_ggAutomizer_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2.1, g.2.2, fun b => rfl⟩
  · rintro ⟨g, hgX, hgN, hφ⟩
    exact ⟨⟨g, hgX, hgN⟩, MulEquiv.ext fun b => Subtype.ext (hφ b).symm⟩

theorem ggTD_tsc_comm {G : Type} [Group G] [Finite G] {m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {w : GGTorusTorWit m N ↥X (ggGamma X hN).range} (hw : w.Holds C M) :
    ∀ t ∈ w.Tsc, ∀ b ∈ Bs, b * (t : G) = (t : G) * b := by
  obtain ⟨-, hAT, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, hTfix, -⟩, -⟩ := hw
  intro t ht b hb
  have h1 := congrArg Subtype.val (hTfix _ (hAT ⟨⟨b, hb⟩, rfl⟩) t ht)
  rw [ggGamma_coe] at h1
  calc b * (t : G) = b * (t : G) * b⁻¹ * b := by group
    _ = _ := by rw [h1]

theorem ggTD_ker {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {w : GGTorusTorWit m N ↥X (ggGamma X hN).range} (hw : w.Holds C M)
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)))
    (hg : ggTDρA hN g = 1) : ggTDρB X Bs g = 1 := by
  have hp : p.Prime := Fact.out
  have hT := ggTD_tsc_comm hN hw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hoddZ, ⟨hcent, -, -⟩, -⟩ := hw
  set gX : ↥X := ⟨g, g.2.1⟩ with hgX
  have hgA : ∀ a ∈ (ggGamma X hN).range, MulAut.conj gX * a * (MulAut.conj gX)⁻¹ = a := by
    intro a ha
    have := congrArg (fun f : MulAut ↥(ggGamma X hN).range =>
      ((f ⟨a, ha⟩ : ↥(ggGamma X hN).range) : MulAut ↥X)) hg
    exact this
  have h1 : ggTDρB X Bs (g ^ p) = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggTDρB_apply]
    simp only [MulAut.one_apply, Subgroup.coe_pow]
    set c : G := (b : G)⁻¹ * ((g : G) * b * (g : G)⁻¹) with hc
    have hcX : ∀ l ∈ X, c * l * c⁻¹ = l := by
      intro l hl
      have e := congrArg (fun φ : MulAut ↥X => ((φ ⟨l, hl⟩ : ↥X) : G)) (hgA _ ⟨b, rfl⟩)
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, Subgroup.coe_mul,
        Subgroup.coe_inv, ggGamma_coe, hgX] at e
      calc c * l * c⁻¹ = (b : G)⁻¹ * ((g : G) * (b * ((g : G)⁻¹ * l * g) * (b : G)⁻¹) *
            (g : G)⁻¹) * b := by rw [hc]; group
        _ = l := by rw [e]; group
    have hcB : c ∈ Bs := Bs.mul_mem (Bs.inv_mem b.2)
      ((Subgroup.mem_normalizer_iff.mp g.2.2 b).mp b.2)
    have hgc : (g : G) * c * (g : G)⁻¹ = c := by
      have := hcX _ (X.inv_mem g.2.1)
      calc (g : G) * c * (g : G)⁻¹ = (g : G) * (c * (g : G)⁻¹ * c⁻¹) * c := by group
        _ = c := by rw [this]; group
    have hbc : (g : G) * b * (g : G)⁻¹ = b * c := by rw [hc]; group
    have hn : ∀ n : ℕ, (g : G) ^ n * b * ((g : G) ^ n)⁻¹ = b * c ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc (g : G) ^ (n + 1) * b * ((g : G) ^ (n + 1))⁻¹ =
            (g : G) * ((g : G) ^ n * b * ((g : G) ^ n)⁻¹) * (g : G)⁻¹ := by
              rw [pow_succ']; group
          _ = ((g : G) * b * (g : G)⁻¹) * ((g : G) * c * (g : G)⁻¹) ^ n := by
              rw [ih, conj_pow]; group
          _ = b * c ^ (n + 1) := by rw [hbc, hgc, pow_succ', mul_assoc]
    rw [hn p, hBs.2 c hcB, mul_one]
  have hmem := hcent gX fun a ha => by
    have := hgA a ha
    rwa [mul_inv_eq_iff_eq_mul] at this
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hmem
  obtain ⟨t, ht, z, hz, htz⟩ := hmem
  obtain ⟨e, o, ho, heo⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
  have hz2 : z ^ 2 ^ e ∈ w.Tsc :=
    hoddZ _ (Subgroup.pow_mem _ hz _) (Odd.of_dvd_nat ho (orderOf_dvd_of_pow_eq_one
      (by rw [← pow_mul, ← heo, pow_orderOf_eq_one])))
  have hgt : gX ^ 2 ^ e = t ^ 2 ^ e * z ^ 2 ^ e := by
    rw [← htz]
    exact (Commute.mul_pow (Subgroup.mem_center_iff.mp hz t) _)
  have h2 : ggTDρB X Bs (g ^ 2 ^ e) = 1 := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggTDρB_apply]
    simp only [MulAut.one_apply]
    have hco : ((g ^ 2 ^ e : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) : G) =
        ((gX ^ 2 ^ e : ↥X) : G) := by simp [hgX]
    rw [hco, hgt, ← hT _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ht _) hz2) b b.2,
      mul_inv_cancel_right]
  have hcop : Nat.Coprime p (2 ^ e) :=
    Nat.Coprime.pow_right e ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h3 : ggTDρB X Bs g ^ Nat.gcd p (2 ^ e) = 1 :=
    pow_gcd_eq_one.mpr ⟨by rw [← map_pow, h1], by rw [← map_pow, h2]⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

theorem ggTD_ker' {G : Type} [Group G] {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) (hg : ggTDρB X Bs g = 1) :
    ggTDρA hN g = 1 := by
  refine MulEquiv.ext fun a => Subtype.ext ?_
  obtain ⟨_, b, rfl⟩ := a
  have hb : (g : G) * b * (g : G)⁻¹ = b := by
    have := congrArg (fun φ : MulAut ↥Bs => ((φ b : ↥Bs) : G)) hg
    exact this
  rw [ggTDρA_apply]
  refine MulEquiv.ext fun l => Subtype.ext ?_
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, Subgroup.coe_mul,
    Subgroup.coe_inv, ggGamma_coe, MulAut.one_apply]
  calc (g : G) * ((b : G) * ((g : G)⁻¹ * l * g) * (b : G)⁻¹) * (g : G)⁻¹ =
      ((g : G) * b * (g : G)⁻¹) * l * ((g : G) * b * (g : G)⁻¹)⁻¹ := by group
    _ = _ := by rw [hb]

def ggTDnH {G : Type} [Group G] {m N : ℕ} {Bs X : Subgroup G} {A : Subgroup (MulAut ↥X)}
    (w : GGTorusTorWit m N ↥X A)
    (hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G)) (k : Fin N) :
    ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) :=
  ⟨w.n k, (w.n k).2, hnk k⟩

theorem ggTD_ρA_nH {G : Type} [Group G] {m N : ℕ} {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m N ↥X (ggGamma X hN).range)
    (hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G)) (k : Fin N) :
    ggTDρA hN (ggTDnH w hnk k) = ggConjAut _ (w.hn k) :=
  MulEquiv.ext fun _ => Subtype.ext rfl

theorem ggTD_ρA_mem {G : Type} [Group G] {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G))) :
    ggTDρA hN g ∈ ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range := by
  have : ggTDρA hN g = ggConjAut _ (conj_mem_normalizer_range_ggGamma hN g.2.1 g.2.2) :=
    MulEquiv.ext fun _ => Subtype.ext rfl
  rw [this]
  exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨_, rfl⟩) _

theorem ggTD_core {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G} (hm : Odd m)
    (hpm : p ∣ m) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m N ↥X (ggGamma X hN).range) (hw : w.Holds C M) :
    ∃ (_hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G))
      (hbk : ∀ k, ((w.cor k (ggZetaP p m) : ↥X) : G) ∈ Bs) (F : Fin N → ↥Bs → ZMod p),
      (∀ k b b', F k (b * b') = F k b + F k b') ∧
      (∀ k (b : ↥Bs), ((w.n k : ↥X) : G) * b * ((w.n k : ↥X) : G)⁻¹ =
        (((w.cor k (ggZetaP p m) : ↥X) : G) ^ (F k b).val)⁻¹ * b) ∧
      (∀ i j, F i ⟨_, hbk j⟩ = (C i j : ZMod p)) ∧
      (∀ k b, ggGamma X hN b = 1 → F k b = 0) ∧
      (∀ b, (∀ k, F k b = 0) → ggGamma X hN b = 1) := by
  have hp : p.Prime := Fact.out
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hA := ggTD_elemAb hN hBs
  have hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    fun k => mem_normalizer_of_ggTorusWeylElt hN hS (w.weylElt hw hA k)
  obtain ⟨αb, hroot, hpairb, -⟩ := w.pairing hp hm hpm hw hA
  obtain ⟨-, hAT, -, hαmul, -, -, hfix, -, -, hWelt, hsep, -⟩ := hw
  have hbk : ∀ k, ((w.cor k (ggZetaP p m) : ↥X) : G) ∈ Bs := by
    intro k
    refine hS _ ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := congrArg Subtype.val (hfix _ (hAT ⟨⟨b, hb⟩, rfl⟩) k (ggZetaP p m))
      rw [ggGamma_coe] at h1
      calc b * ((w.cor k (ggZetaP p m) : ↥X) : G) =
          b * ((w.cor k (ggZetaP p m) : ↥X) : G) * b⁻¹ * b := by group
        _ = _ := by rw [h1]
    · rw [← Subgroup.coe_pow, ← map_pow, ggZetaP_pow_self hpm, map_one, Subgroup.coe_one]
  let F : Fin N → ↥Bs → ZMod p := fun k b => αb k ⟨ggGamma X hN b, b, rfl⟩
  have hr : ∀ k b, w.α k (ggGamma X hN b) = ggZetaP p m ^ (F k b).val :=
    fun k b => hroot k ⟨_, b, rfl⟩
  refine ⟨hnk, hbk, F, ?_, ?_, ?_, ?_, ?_⟩
  · intro k b b'
    apply ggTD_zeta_val_inj hm0 hpm
    rw [ZMod.val_add, ggZetaP_pow_mod hpm, pow_add, ← hr, ← hr, ← hr, map_mul]
    exact hαmul k _ (hAT ⟨b, rfl⟩) _ (hAT ⟨b', rfl⟩)
  · intro k b
    have h1 := congrArg Subtype.val (hWelt k _ (hAT ⟨b, rfl⟩))
    rw [hr, map_pow] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, ggGamma_coe] at h1
    calc ((w.n k : ↥X) : G) * b * ((w.n k : ↥X) : G)⁻¹ =
        (((w.n k : ↥X) : G) * ((b : G) * ((w.n k : ↥X) : G) * (b : G)⁻¹)⁻¹) * b := by group
      _ = _ := by rw [h1]
  · intro i j
    have hγ : ggGamma X hN ⟨_, hbk j⟩ = MulAut.conj (w.cor j (ggZetaP p m)) := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      rw [ggGamma_coe]
      rfl
    have hj : MulAut.conj (w.cor j (ggZetaP p m)) ∈ (ggGamma X hN).range := hγ ▸ ⟨_, rfl⟩
    have e : (⟨ggGamma X hN ⟨_, hbk j⟩, _, rfl⟩ : ↥(ggGamma X hN).range) = ⟨_, hj⟩ :=
      Subtype.ext hγ
    show αb i _ = _
    rw [e]
    exact hpairb i j hj
  · intro k b hb
    apply ggTD_zeta_val_inj hm0 hpm
    rw [ZMod.val_zero, pow_zero, ← hr, hb]
    exact ggTor_alpha_one _ _ (hαmul k)
  · intro b hb
    refine hsep _ (hAT ⟨b, rfl⟩) fun k => ?_
    rw [hr, hb k, ZMod.val_zero, pow_zero]

theorem ggTD_fix_mem_centralizer
    {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range)
    (b : Bs) (hb : ∀ φ ∈ ggAutomizer X Bs, φ b = b) :
    (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hnk, hbk, F, _, hact, _, _, hsep⟩ := ggTD_core hm hpm hBs hS hN w hw
  apply (ggGamma_eq_one_iff X hN b).mp
  apply hsep b
  intro k
  let g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)) := ggTDnH w hnk k
  have hφ : ggTDρB X Bs g ∈ ggAutomizer X Bs := by
    rw [← ggTDρB_range]
    exact ⟨g, rfl⟩
  have hfix : ((w.n k : ↥X) : G) * (b : G) * (((w.n k : ↥X) : G))⁻¹ = b := by
    exact congrArg Subtype.val (hb _ hφ)
  have hpowG : (((w.cor k (ggZetaP p m) : ↥X) : G) ^ (F k b).val) = 1 := by
    have heq := (hact k b).symm.trans hfix
    have heq' := congrArg (fun z : G => z * (b : G)⁻¹) heq
    simpa using heq'
  have hpow : (w.cor k (ggZetaP p m)) ^ (F k b).val = 1 :=
    Subtype.ext (by simpa using hpowG)
  have hinj : Function.Injective (w.cor k) := hw.2.2.2.2.1 k
  have hz : ggZetaP p m ^ (F k b).val = 1 := by
    apply hinj
    simpa only [map_pow, map_one] using hpow
  exact ggTD_zeta_val_inj hm.pos.ne' hpm (F k b) 0 (by simpa using hz)

theorem ggTD_fix_iff_mem_centralizer
    {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range)
    (b : Bs) :
    (∀ φ ∈ ggAutomizer X Bs, φ b = b) ↔ (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  constructor
  · intro hfix
    exact ggTD_fix_mem_centralizer hm hpm hBs hS hN hTor b hfix
  · intro hb φ hφ
    exact ggAutomizer_apply_eq_of_le_centralizer (H := X) (x := b)
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hb) x hx)) hφ

theorem ggTD_closure {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {w : GGTorusTorWit m N ↥X (ggGamma X hN).range} (hw : w.Holds C M)
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ggAutomizer X Bs = Subgroup.closure (Set.range fun k => ggTDρB X Bs (ggTDnH w hnk k)) := by
  have hAut := hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← ggTDρB_range]
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr ?_)
  · rintro _ ⟨g, rfl⟩
    have hgA : ggTDρA hN g ∈ (Subgroup.closure (Set.range (ggTDnH w hnk))).map (ggTDρA hN) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have hc : (ggTDρA hN ∘ ggTDnH w hnk) = fun k => ggConjAut _ (w.hn k) :=
        funext fun k => ggTD_ρA_nH hN w hnk k
      rw [hc, ← hAut]
      exact ggTD_ρA_mem hN g
    obtain ⟨u, hu, hug⟩ := hgA
    have hk := ggTD_ker hN hw hp2 hBs (u⁻¹ * g) (by rw [map_mul, map_inv, hug, inv_mul_cancel])
    rw [map_mul, map_inv, inv_mul_eq_one] at hk
    rw [← hk]
    have : ggTDρB X Bs u ∈ (Subgroup.closure (Set.range (ggTDnH w hnk))).map (ggTDρB X Bs) :=
      ⟨u, hu, rfl⟩
    rwa [MonoidHom.map_closure, ← Set.range_comp] at this
  · rintro _ ⟨k, rfl⟩
    exact ⟨_, rfl⟩

theorem ggTD_weyl {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {w : GGTorusTorWit m N ↥X (ggGamma X hN).range} (hw : w.Holds C M)
    (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ e : M.Group ≃* ↥(ggAutomizer X Bs),
      ∀ k, (e (M.simple k) : MulAut ↥Bs) = ggTDρB X Bs (ggTDnH w hnk k) := by
  have hAut := hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨e0, he0⟩ := hw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hker : (ggTDρB X Bs).ker = (ggTDρA hN).ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    exact ⟨ggTD_ker' hN g, ggTD_ker hN hw hp2 hBs g⟩
  have hrA : (ggTDρA hN).range =
      ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range := by
    apply le_antisymm
    · rintro _ ⟨g, rfl⟩
      exact ggTD_ρA_mem hN g
    · rw [hAut, Subgroup.closure_le]
      rintro _ ⟨k, rfl⟩
      exact ⟨ggTDnH w hnk k, ggTD_ρA_nH hN w hnk k⟩
  let E : ↥(ggTDρB X Bs).range ≃* ↥(ggTDρA hN).range :=
    (QuotientGroup.quotientKerEquivRange _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange _))
  have hE : ∀ g, E ⟨ggTDρB X Bs g, g, rfl⟩ = ⟨ggTDρA hN g, g, rfl⟩ := by
    intro g
    have h1 : (QuotientGroup.quotientKerEquivRange (ggTDρB X Bs)).symm ⟨_, g, rfl⟩ =
        (g : _ ⧸ (ggTDρB X Bs).ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [E, MulEquiv.trans_apply]
    rw [h1]
    rfl
  refine ⟨e0.trans ((MulEquiv.subgroupCongr hrA).symm.trans
    (E.symm.trans (MulEquiv.subgroupCongr ggTDρB_range))), fun k => ?_⟩
  simp only [MulEquiv.trans_apply]
  have h1 : (MulEquiv.subgroupCongr hrA).symm (e0 (M.simple k)) =
      ⟨ggTDρA hN (ggTDnH w hnk k), _, rfl⟩ :=
    Subtype.ext ((he0 k).trans (ggTD_ρA_nH hN w hnk k).symm)
  rw [h1, ← hE, MulEquiv.symm_apply_apply]
  rfl

theorem ggTD_coe_prod {G : Type} [Group G] {p m N : ℕ} {Bs X : Subgroup G}
    {A : Subgroup (MulAut ↥X)} (w : GGTorusTorWit m N ↥X A)
    (hbk : ∀ k, ((w.cor k (ggZetaP p m) : ↥X) : G) ∈ Bs) (c : Fin N → ZMod p) :
    (((List.ofFn fun k => (⟨_, hbk k⟩ : ↥Bs) ^ (c k).val).prod : ↥Bs) : G) =
      (((List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod : ↥X) : G) := by
  rw [SubmonoidClass.coe_list_prod, SubmonoidClass.coe_list_prod, List.map_ofFn, List.map_ofFn]
  refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
  simp [map_pow]

theorem ggTD_lin {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)} {Bs X : Subgroup G}
    (hm : Odd m) (hpm : p ∣ m) (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (w : GGTorusTorWit m N ↥X (ggGamma X hN).range) (hw : w.Holds C M)
    (hInd : ∀ c : Fin N → ZMod p,
      (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 → c = 0)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    ∃ (hnk : ∀ k, ((w.n k : ↥X) : G) ∈ Subgroup.normalizer (Bs : Set G))
      (hbk : ∀ k, ((w.cor k (ggZetaP p m) : ↥X) : G) ∈ Bs)
      (α : Fin N → Module.Dual (ZMod p) V),
      (∀ i v, ggLin (p := p) ι (ggTDρB X Bs (ggTDnH w hnk i)) v =
        v - α i v • ι (Additive.ofMul ⟨_, hbk i⟩)) ∧
      (∀ i j, α i (ι (Additive.ofMul ⟨_, hbk j⟩)) = (C i j : ZMod p)) ∧
      (∀ i (b : ↥Bs), ggGamma X hN b = 1 → α i (ι (Additive.ofMul b)) = 0) ∧
      (∀ v, (∀ i, α i v = 0) → ggGamma X hN (Additive.toMul (ι.symm v)) = 1) ∧
      LinearIndependent (ZMod p) (fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs))) := by
  obtain ⟨hnk, hbk, F, hFadd, hFφ, hFC, hF1, hFsep⟩ := ggTD_core hm hpm hBs hS hN w hw
  let f : Fin N → Additive ↥Bs →+ ZMod p := fun k =>
    AddMonoidHom.mk' (fun b => F k (Additive.toMul b)) (fun b b' => hFadd k _ _)
  let α : Fin N → Module.Dual (ZMod p) V := fun k =>
    ((f k).comp ι.symm.toAddMonoidHom).toZModLinearMap p
  have hα : ∀ k v, α k v = F k (Additive.toMul (ι.symm v)) := fun _ _ => rfl
  refine ⟨hnk, hbk, α, fun i v => ?_, fun i j => ?_, fun i b hb => ?_, fun v hv => ?_, ?_⟩
  · rw [ggLin_apply]
    have hφb : ggTDρB X Bs (ggTDnH w hnk i) (Additive.toMul (ι.symm v)) =
        ((⟨_, hbk i⟩ : ↥Bs) ^ (F i (Additive.toMul (ι.symm v))).val)⁻¹ *
          Additive.toMul (ι.symm v) := by
      apply Subtype.ext
      rw [ggTDρB_apply]
      push_cast
      exact hFφ i _
    rw [hφb, ofMul_mul, ofMul_inv, ofMul_pow, map_add, map_neg, map_nsmul, ofMul_toMul,
      AddEquiv.apply_symm_apply, hα, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
    abel
  · rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hFC i j
  · rw [hα, AddEquiv.symm_apply_apply, toMul_ofMul]
    exact hF1 i b hb
  · exact hFsep _ fun k => (hα k v).symm.trans (hv k)
  · rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [ggTD_sum_eq ι (fun k => (⟨_, hbk k⟩ : ↥Bs)) c] at hc
    have hP : (List.ofFn fun k => (⟨_, hbk k⟩ : ↥Bs) ^ (c k).val).prod = 1 := by
      have := ι.injective (hc.trans (map_zero ι).symm)
      exact Additive.ofMul.injective this
    have hX : (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 := by
      apply Subtype.ext
      rw [← ggTD_coe_prod w hbk c, hP]
      rfl
    exact congrFun (hInd c hX)

theorem ggTBWeyl_of_torW {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)}
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range) :
    ∃ (φ : Fin N → MulAut ↥Bs) (e : M.Group ≃* ↥(ggAutomizer X Bs)),
      (∀ k, φ k ∈ ggAutomizer X Bs) ∧ ∀ k, (e (M.simple k) : MulAut ↥Bs) = φ k := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hnk, -⟩ := ggTD_core hm hpm hBs hS hN w hw
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  exact ⟨fun k => ggTDρB X Bs (ggTDnH w hnk k), e,
    fun k => by rw [← ggTDρB_range]; exact ⟨_, rfl⟩, he⟩

theorem ggTBDatum_of_torW {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2)
    (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hM : GGIsWeylMatrix M) (hMC : GGIntCartan M C)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range)
    (hInd : ∀ w : GGTorusTorWit m N ↥X (ggGamma X hN).range, w.Holds C M →
      ∀ c : Fin N → ZMod p, (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 →
        c = 0)
    (hcard : Nat.card Bs ≤ p ^ N)
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    ∃ (φ : Fin N → MulAut ↥Bs) (h : Fin N → V) (α : Fin N → Module.Dual (ZMod p) V),
      GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ k, φ k ∈ ggAutomizer X Bs) ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧
      LinearIndependent (ZMod p) h ∧ Submodule.span (ZMod p) (Set.range h) = ⊤ ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hnk, hbk, α, hlin, hpair, -, -, hind⟩ :=
    ggTD_lin hm hpm hBs hS hN w hw (hInd w hw) V ι
  refine ⟨fun k => ggTDρB X Bs (ggTDnH w hnk k), _, α, hM, hMC,
    fun k => by rw [← ggTDρB_range]; exact ⟨_, rfl⟩, hlin, hpair, hind,
    ggTD_span_top ι _ hind (by simpa using hcard), ggTD_closure hN hw hp2 hBs hnk⟩

theorem ggTBDatumOpt_of_torW_weyl {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hM : GGIsWeylMatrix M) (hMC : GGIntCartan M C)
    {Bs X : Subgroup G} {x : G} (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hxBs : x ∈ Bs) (hxX : x ∉ X)
    (hCx : ∀ b ∈ Bs, b ∈ Subgroup.centralizer (X : Set G) → b ∈ Subgroup.zpowers x)
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range)
    (hInd : ∀ w : GGTorusTorWit m N ↥X (ggGamma X hN).range, w.Holds C M →
      ∀ c : Fin N → ZMod p, (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 →
        c = 0)
    (hcard : Nat.card Bs ≤ p ^ (N + 1))
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    ∃ (φ : Fin N → MulAut ↥Bs) (h : Fin N → V) (α : Fin N → Module.Dual (ZMod p) V),
      GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ k, φ k ∈ ggAutomizer X Bs) ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧ (∀ i, α i (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0) ∧
      LinearIndependent (ZMod p) (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h) ∧
      Submodule.span (ZMod p) (Set.range (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h)) = ⊤ ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) ∧
      (∃ e : M.Group ≃* ↥(ggAutomizer X Bs),
        ∀ k, (e (M.simple k) : MulAut ↥Bs) = φ k) := by
  have hp : p.Prime := Fact.out
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hnk, hbk, α, hlin, hpair, hα1, hαsep, hind⟩ :=
    ggTD_lin hm hpm hBs hS hN w hw (hInd w hw) V ι
  set h : Fin N → V := fun k => ι (Additive.ofMul (⟨_, hbk k⟩ : ↥Bs)) with hh
  have hind' : LinearIndependent (ZMod p) (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h) := by
    show LinearIndependent (ZMod p) (fun o => Option.casesOn' o _ h)
    rw [linearIndependent_option']
    refine ⟨hind, fun hmem => hxX ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hmem
    rw [hh, ggTD_sum_eq ι (fun k => (⟨_, hbk k⟩ : ↥Bs)) c] at hc
    have hP := Additive.ofMul.injective (ι.injective hc)
    have := congrArg Subtype.val hP
    rw [ggTD_coe_prod w hbk c] at this
    rw [show x = (((List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod : ↥X) : G) from
      this.symm]
    exact Subtype.coe_prop _
  have hγx : ggGamma X hN ⟨x, hxBs⟩ = 1 := by
    by_contra hne
    have hxp : (⟨x, hxBs⟩ : ↥Bs) ^ p = 1 := Subtype.ext (by simpa using hBs.2 x hxBs)
    have hγo : orderOf (ggGamma X hN ⟨x, hxBs⟩) = p :=
      orderOf_eq_prime (by rw [← map_pow, hxp, map_one]) hne
    have hinj : ∀ b : ↥Bs, ggGamma X hN b = 1 → b = 1 := by
      intro b hb
      have hbC := (ggGamma_eq_one_iff X hN b).mp hb
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hCx b b.2 hbC)
      have hj' : (⟨x, hxBs⟩ : ↥Bs) ^ j = b := Subtype.ext (by simpa using hj)
      have hpj : (p : ℤ) ∣ j := by
        rw [← hγo, orderOf_dvd_iff_zpow_eq_one, ← map_zpow, hj', hb]
      obtain ⟨q, rfl⟩ := hpj
      rw [← hj', zpow_mul, zpow_natCast, hxp, one_zpow]
    let Φ : V →ₗ[ZMod p] (Fin N → ZMod p) := LinearMap.pi α
    have hΦ : Function.Injective Φ := by
      refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun v hv => ?_)
      have h1 := hinj _ (hαsep v fun i => congrFun hv i)
      rw [← ι.apply_symm_apply v, ← ofMul_toMul (ι.symm v), h1, ofMul_one, map_zero]
    have : Finite V := Finite.of_equiv _ ι.toEquiv
    have : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have h1 := LinearMap.finrank_le_finrank_of_injective hΦ
    have h2 := hind'.fintype_card_le_finrank
    simp only [Module.finrank_fin_fun, Fintype.card_option, Fintype.card_fin] at h1 h2
    omega
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  refine ⟨fun k => ggTDρB X Bs (ggTDnH w hnk k), h, α, hM, hMC,
    fun k => by rw [← ggTDρB_range]; exact ⟨_, rfl⟩, hlin, hpair, fun i => hα1 i _ hγx, hind',
    ggTD_span_top ι _ hind' (by simpa using hcard), ggTD_closure hN hw hp2 hBs hnk, ⟨e, he⟩⟩

theorem ggTBDatumOpt_of_torW {G : Type} [Group G] [Finite G] {p m N : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hm : Odd m) (hpm : p ∣ m) {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hM : GGIsWeylMatrix M) (hMC : GGIntCartan M C)
    {Bs X : Subgroup G} {x : G} (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hxBs : x ∈ Bs) (hxX : x ∉ X)
    (hCx : ∀ b ∈ Bs, b ∈ Subgroup.centralizer (X : Set G) → b ∈ Subgroup.zpowers x)
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range)
    (hInd : ∀ w : GGTorusTorWit m N ↥X (ggGamma X hN).range, w.Holds C M →
      ∀ c : Fin N → ZMod p, (List.ofFn fun k => w.cor k (ggZetaP p m ^ (c k).val)).prod = 1 →
        c = 0)
    (hcard : Nat.card Bs ≤ p ^ (N + 1))
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    ∃ (φ : Fin N → MulAut ↥Bs) (h : Fin N → V) (α : Fin N → Module.Dual (ZMod p) V),
      GGIsWeylMatrix M ∧ GGIntCartan M C ∧
      (∀ k, φ k ∈ ggAutomizer X Bs) ∧
      (∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) ∧
      (∀ i j, α i (h j) = (C i j : ZMod p)) ∧ (∀ i, α i (ι (Additive.ofMul ⟨x, hxBs⟩)) = 0) ∧
      LinearIndependent (ZMod p) (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h) ∧
      Submodule.span (ZMod p) (Set.range (ggOptFam (ι (Additive.ofMul ⟨x, hxBs⟩)) h)) = ⊤ ∧
      ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
  obtain ⟨φ, h, α, hM', hMC', hφ, hlin, hpair, hα1, hli, hspan, hclos, e, he⟩ :=
    ggTBDatumOpt_of_torW_weyl hp2 hm hpm hM hMC hBs hS hN hxBs hxX hCx hTor hInd hcard V ι
  exact ⟨φ, h, α, hM', hMC', hφ, hlin, hpair, hα1, hli, hspan, hclos⟩

end CFSG.StandardType
