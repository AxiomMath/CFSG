module

public import CFSG.LocalAnalysis.StandardType.FS81.StdLoc
public import CFSG.LocalAnalysis.StandardType.FS81.D6UniqueAux
public import CFSG.LocalAnalysis.StandardType.FS81.D6Inner
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameTrans
public import CFSG.LocalAnalysis.StandardType.FS81.BasisMonomial
public import CFSG.LocalAnalysis.StandardType.FS81.LocalGen
public import CFSG.Quasithin.Vol2.KGFactC31RuRef

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped Matrix commutatorElement

private theorem exists_acts_evenFix0_of_rootS3 {G : Type} [Group G] [Finite G]
    {b₀ : G} {K E : Subgroup G} (hstd : StdLoc b₀ K E Row.D6)
    {B : Basis3 G (Row.D6.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.D6 B b₀)
    {v : Coords (Row.D6.n + 1)} (hv0 : v 0 = 0) (hv : wt v = 2)
    {s : G} (hs : s ∈ K) (hs2 : s * s = 1)
    (hsv : s * B.vec v * s⁻¹ = (B.vec v)⁻¹)
    (hN : ∀ t ∈ E ⊓ K, ∀ x ∈ Subgroup.closure {B.vec v, s},
      t * x * t⁻¹ ∈ Subgroup.closure {B.vec v, s}) :
    ∃ A, B.Acts s A ∧ A ∈ evenFix0 6 ∧ A *ᵥ v = -v ∧
      ∀ w : Coords (Row.D6.n + 1), ∃ c : ZMod 3, A *ᵥ w - w = c • v := by
  classical
  have hHyp : HypSetupLoc b₀ K E Row.D6.m := hstd.2.1
  have hCanon : CanonPosition b₀ K E Row.D6 := hstd.2.2
  obtain ⟨hA, hEmax, hb₀E, hcardE, hm, hbig⟩ := hHyp
  obtain ⟨hb₀ord, hKC, hKn, hZ, hmarking, hA2, hA3, hA4⟩ := hA
  obtain ⟨hrow, hdisj, hsup, hmaxA, hcardA, hcentA⟩ := hCanon
  have hspan : B.span = E := hB.1
  have hb0 : B.b 0 = b₀ := hB.2.1
  have hbiK : ∀ i : Fin (Row.D6.n + 1), i ≠ 0 → B.b i ∈ K := hB.2.2
  set h : G := B.vec v with hhdef
  have hhE : h ∈ E := by rw [← hspan, hhdef]; exact B.vec_mem_span v
  have hhK : h ∈ K := by rw [hhdef]; exact E7Frame.vec_mem_K hB hv0
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, wt] at hv
    simp at hv
  have hhne : h ≠ 1 := by
    intro h1
    apply hvne
    apply B.vec_injective
    rw [← hhdef, h1, B.vec_zero]
  have h3 : h ^ 3 = 1 := by
    rw [hhdef]
    have hv3 : v + v + v = 0 := by
      funext i
      have : ∀ x : ZMod 3, x + x + x = 0 := by decide
      exact this (v i)
    have hvec : B.vec (v + v + v) = (B.vec v) ^ 3 := by
      rw [show v + v + v = (v + v) + v by rfl, B.vec_add, B.vec_add, pow_succ, pow_two]
    rw [← hvec, hv3, B.vec_zero]
  have hord3 : orderOf h = 3 := orderOf_eq_prime h3 hhne
  have hsh : s * h * s⁻¹ = h⁻¹ := by rw [hhdef]; exact hsv
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hs_b0 : s * b₀ * s⁻¹ = b₀ := by
    have hcomm : s * b₀ = b₀ * s := Subgroup.mem_centralizer_singleton_iff.mp (hKC hs)
    rw [hcomm]; group
  have hs_b0pow : ∀ n : ℕ, s * b₀ ^ n * s⁻¹ = b₀ ^ n := by
    intro n
    rw [show s * b₀ ^ n * s⁻¹ = (MulAut.conj s) (b₀ ^ n) from rfl, map_pow]
    rw [show (MulAut.conj s) b₀ = b₀ from hs_b0]
  have hs_b0zpow : ∀ n : ℤ, s * b₀ ^ n * s⁻¹ = b₀ ^ n := by
    intro n
    rw [show s * b₀ ^ n * s⁻¹ = (MulAut.conj s) (b₀ ^ n) from rfl, map_zpow]
    rw [show (MulAut.conj s) b₀ = b₀ from hs_b0]
  have hgen : Subgroup.closure ({B.vec v, s} : Set G) =
      Subgroup.closure ({h, s} : Set G) := by rw [← hhdef]
  have hconjT : ∀ t ∈ E ⊓ K, s * t * s⁻¹ ∈ E ⊓ K := by
    intro t ht
    have hxmem0 : t * s * t⁻¹ ∈ Subgroup.closure ({B.vec v, s} : Set G) :=
      hN t ht s (Subgroup.subset_closure (by simp))
    have hxmem : t * s * t⁻¹ ∈ Subgroup.closure ({h, s} : Set G) := by
      rwa [hgen] at hxmem0
    have hx2 : (t * s * t⁻¹) * (t * s * t⁻¹) = 1 := by
      calc (t * s * t⁻¹) * (t * s * t⁻¹) = t * (s * s) * t⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    rcases involution_mem_closure_pair h3 hs2 hsh hxmem hx2 with hx1 | ⟨i, hi⟩
    · exfalso
      have hs1 : s = 1 := by
        have h : t⁻¹ * (t * s * t⁻¹) * t = s := by group
        rw [hx1] at h
        simpa using h.symm
      have hh1 : h = 1 := by
        have h2 : h = h⁻¹ := by
          rw [← hsh, hs1]
          group
        have hh2 : h * h = 1 := by
          have h' := congrArg (fun x => h * x) h2
          rwa [mul_inv_cancel] at h'
        have h3' : h ^ 2 * h = 1 := by rw [← pow_succ]; exact h3
        calc h = h ^ 2 * h := by rw [pow_two, hh2, one_mul]
          _ = 1 := h3'
      exact hhne hh1
    · have hst : s * t * s⁻¹ = h ^ (-i) * t := conj_eq_zpow_mul_of_conj_eq hs2 hi
      have hy : h ^ (-i) ∈ Subgroup.zpowers h := Subgroup.zpow_mem_zpowers h (-i)
      have hmemE : h ^ (-i) ∈ E := (Subgroup.zpowers_le.mpr hhE) hy
      have hmemK : h ^ (-i) ∈ K := (Subgroup.zpowers_le.mpr hhK) hy
      rw [hst]
      exact (E ⊓ K).mul_mem ⟨hmemE, hmemK⟩ ht
  have hsZ : s ∈ Subgroup.normalizer (Subgroup.zpowers b₀ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [hs_b0zpow n]
      exact Subgroup.zpow_mem_zpowers b₀ n
    · intro hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hx_eq : x = b₀ ^ n := by
        calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
          _ = s⁻¹ * b₀ ^ n * s := by rw [← hn]
          _ = b₀ ^ n := by simpa only [hs_inv] using hs_b0zpow n
      rw [hx_eq]
      exact Subgroup.zpow_mem_zpowers b₀ n
  have hsT : s ∈ Subgroup.normalizer ((E ⊓ K : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconjT x
    · intro hx
      have hy := hconjT (s * x * s⁻¹) hx
      have hxeq : s * (s * x * s⁻¹) * s⁻¹ = x := by
        calc s * (s * x * s⁻¹) * s⁻¹ = (s * s) * x * (s⁻¹ * s⁻¹) := by group
          _ = x := by rw [hs2, hs_inv, hs2]; group
      rwa [hxeq] at hy
  have hsNsup : s ∈ Subgroup.normalizer
      ((Subgroup.zpowers b₀ ⊔ (E ⊓ K) : Subgroup G) : Set G) :=
    Subgroup.normalizer_inf_normalizer_le_normalizer_sup (Subgroup.zpowers b₀) (E ⊓ K)
      ⟨hsZ, hsT⟩
  have hsNE : s ∈ Subgroup.normalizer (E : Set G) := by
    rw [← hsup]
    exact hsNsup
  have hsNB : s ∈ Subgroup.normalizer (B.span : Set G) := by
    rw [hspan]
    exact hsNE
  obtain ⟨A, hActs⟩ := B.exists_acts hsNB
  have hAeven : A ∈ evenFix0 6 := by
    have hAK : A ∈ B.realized K := ⟨s, hs, hActs⟩
    have hEven : B.realized K = evenFix0 6 :=
      (realized_centralizer_eq_realized_D6 hstd hB hrec).2
    rw [← hEven]
    exact hAK
  have hAv : A *ᵥ v = -v := by
    have h1 : B.vec (A *ᵥ v) = (B.vec v)⁻¹ := (B.acts_vec hActs v).symm.trans hsv
    rw [← B.vec_neg] at h1
    exact B.vec_injective h1
  have himA : ∀ w : Coords (Row.D6.n + 1), ∃ c : ZMod 3, A *ᵥ w - w = c • v := by
    intro w
    let u : Coords (Row.D6.n + 1) := w - Pi.single 0 (w 0)
    have hu0 : u 0 = 0 := by simp [u]
    have hwu : u + Pi.single 0 (w 0) = w := by ext i; simp [u]
    have huE : B.vec u ∈ E := by rw [← hspan]; exact B.vec_mem_span u
    have huK : B.vec u ∈ K := E7Frame.vec_mem_K hB hu0
    have hxmem0 : B.vec u * s * (B.vec u)⁻¹ ∈ Subgroup.closure ({B.vec v, s} : Set G) :=
      hN (B.vec u) ⟨huE, huK⟩ s (Subgroup.subset_closure (by simp))
    have hxmem : B.vec u * s * (B.vec u)⁻¹ ∈ Subgroup.closure ({h, s} : Set G) := by
      rwa [hgen] at hxmem0
    have hx2 : (B.vec u * s * (B.vec u)⁻¹) * (B.vec u * s * (B.vec u)⁻¹) = 1 := by
      calc (B.vec u * s * (B.vec u)⁻¹) * (B.vec u * s * (B.vec u)⁻¹)
          = B.vec u * (s * s) * (B.vec u)⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    rcases involution_mem_closure_pair h3 hs2 hsh hxmem hx2 with hx1 | ⟨i, hi⟩
    · exfalso
      have hs1 : s = 1 := by
        have h : (B.vec u)⁻¹ * (B.vec u * s * (B.vec u)⁻¹) * B.vec u = s := by group
        rw [hx1] at h
        simpa using h.symm
      have hh1 : h = 1 := by
        have h2 : h = h⁻¹ := by
          rw [← hsh, hs1]
          group
        have hh2 : h * h = 1 := by
          have h' := congrArg (fun x => h * x) h2
          rwa [mul_inv_cancel] at h'
        have h3' : h ^ 2 * h = 1 := by rw [← pow_succ]; exact h3
        calc h = h ^ 2 * h := by rw [pow_two, hh2, one_mul]
          _ = 1 := h3'
      exact hhne hh1
    · have hconj_u : s * B.vec u * s⁻¹ = h ^ (-i) * B.vec u :=
        conj_eq_zpow_mul_of_conj_eq hs2 hi
      obtain ⟨c, hc⟩ : ∃ c : ZMod 3, h ^ (-i) = B.vec (c • v) :=
        exists_smul_of_mem_zpowers_vec B hord3 (Subgroup.zpow_mem_zpowers h (-i))
      have hvec_w : B.vec w = B.vec u * b₀ ^ (w 0).val := by
        have hw0 : (u + (Pi.single 0 (w 0) : Coords (Row.D6.n + 1))) 0 = w 0 := by rw [hwu]
        rw [← hwu, B.vec_add, B.vec_single_eq_pow, hb0, hw0]
      have hstep : s * B.vec w * s⁻¹ =
          B.vec (c • v) * (B.vec u * b₀ ^ (w 0).val) := by
        rw [hvec_w]
        calc s * (B.vec u * b₀ ^ (w 0).val) * s⁻¹
            = (s * B.vec u * s⁻¹) * (s * b₀ ^ (w 0).val * s⁻¹) := by group
          _ = (h ^ (-i) * B.vec u) * b₀ ^ (w 0).val := by
            rw [hconj_u, hs_b0pow]
          _ = B.vec (c • v) * (B.vec u * b₀ ^ (w 0).val) := by rw [← hc]; group
      have hval : B.vec (A *ᵥ w) = B.vec (c • v + w) := by
        rw [← B.acts_vec hActs w, hstep, B.vec_add, hvec_w]
      refine ⟨c, ?_⟩
      rw [B.vec_injective hval]
      abel
  exact ⟨A, hActs, hAeven, hAv, himA⟩

theorem eq_of_rootS3_D6 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOut Row.D6 B b₀) {v : Coords (Row.D6.n + 1)} (hv0 : v 0 = 0) (hv : wt v = 2)
    {s s' : G} (hs : s ∈ K) (hs' : s' ∈ K) (hs2 : s * s = 1) (hs'2 : s' * s' = 1)
    (hsv : s * B.vec v * s⁻¹ = (B.vec v)⁻¹) (hs'v : s' * B.vec v * s'⁻¹ = (B.vec v)⁻¹)
    (hN : ∀ t ∈ E ⊓ K, ∀ x ∈ Subgroup.closure {B.vec v, s},
      t * x * t⁻¹ ∈ Subgroup.closure {B.vec v, s})
    (hN' : ∀ t ∈ E ⊓ K, ∀ x ∈ Subgroup.closure {B.vec v, s'},
      t * x * t⁻¹ ∈ Subgroup.closure {B.vec v, s'}) :
    Subgroup.closure {B.vec v, s} = Subgroup.closure {B.vec v, s'} := by
  classical
  have hHyp : HypSetupLoc b₀ K E Row.D6.m := hstd.2.1
  have hCanon : CanonPosition b₀ K E Row.D6 := hstd.2.2
  obtain ⟨hA, hEmax, hb₀E, hcardE, hm, hbig⟩ := hHyp
  obtain ⟨hb₀ord, hKC, hKn, hZ, hmarking, hA2, hA3, hA4⟩ := hA
  obtain ⟨hrow, hdisj, hsup, hmaxA, hcardA, hcentA⟩ := hCanon
  have hspan : B.span = E := hB.1
  have hb0 : B.b 0 = b₀ := hB.2.1
  have hbiK : ∀ i : Fin (Row.D6.n + 1), i ≠ 0 → B.b i ∈ K := hB.2.2
  set h : G := B.vec v with hhdef
  have hhE : h ∈ E := by rw [← hspan, hhdef]; exact B.vec_mem_span v
  have hhK : h ∈ K := by rw [hhdef]; exact E7Frame.vec_mem_K hB hv0
  have hsh : s * h * s⁻¹ = h⁻¹ := by rw [hhdef]; exact hsv
  have hsh' : s' * h * s'⁻¹ = h⁻¹ := by rw [hhdef]; exact hs'v
  have h3 : h ^ 3 = 1 := by
    rw [hhdef]
    have hvne : v ≠ 0 := by
      intro h0
      rw [h0, wt] at hv
      simp at hv
    have hv3 : v + v + v = 0 := by
      funext i
      have : ∀ x : ZMod 3, x + x + x = 0 := by decide
      exact this (v i)
    have hvec : B.vec (v + v + v) = (B.vec v) ^ 3 := by
      rw [show v + v + v = (v + v) + v by rfl, B.vec_add, B.vec_add, pow_succ, pow_two]
    rw [← hvec, hv3, B.vec_zero]
  have hhne : h ≠ 1 := by
    intro h1
    have hvne : v ≠ 0 := by
      intro h0
      rw [h0, wt] at hv
      simp at hv
    apply hvne
    apply B.vec_injective
    rw [← hhdef, h1, B.vec_zero]
  obtain ⟨A, hActs, hAeven, hAv, himA⟩ :=
    exists_acts_evenFix0_of_rootS3 hstd hB hrec hv0 hv hs hs2 hsv hN
  obtain ⟨A', hActs', hA'even, hA'v, himA'⟩ :=
    exists_acts_evenFix0_of_rootS3 hstd hB hrec hv0 hv hs' hs'2 hs'v hN'
  have hAA' : A = A' := eq_of_spMat_refl hAeven hA'even hv0 hv hAv hA'v himA himA'
  have hcol : ∀ k : Fin 7, s * B.b k * s⁻¹ = s' * B.b k * s'⁻¹ := by
    intro k
    rw [hActs k, hActs' k, hAA']
  let T : Subgroup G := E ⊓ K
  have hTeq : T = Subgroup.closure (Set.range fun i : Fin 6 => B.b i.succ) := by
    apply le_antisymm
    · intro x hx
      change x ∈ E ⊓ K at hx
      have hxspan : x ∈ B.span := by rw [hspan]; exact hx.1
      obtain ⟨e, he⟩ := B.exists_vec_eq hxspan
      have heK : B.vec e ∈ K := by rw [he]; exact hx.2
      have he0 : e 0 = 0 := E7Frame.zero_of_vec_mem_K hB hb₀ord hdisj hb₀E heK
      rw [← he]
      have hsplit : B.vec e =
          (List.ofFn fun i : Fin 6 => B.b i.succ ^ (e i.succ).val).prod := by
        unfold Basis3.vec
        rw [List.ofFn_succ, List.prod_cons, show (e 0).val = 0 by rw [he0]; rfl,
          pow_zero, one_mul]
        rfl
      rw [hsplit]
      refine Subgroup.list_prod_mem _ fun y hy => ?_
      rw [List.mem_ofFn] at hy
      obtain ⟨i, rfl⟩ := hy
      have hmem : B.b i.succ ∈ Subgroup.closure (Set.range fun j : Fin 6 => B.b j.succ) :=
        Subgroup.subset_closure ⟨i, rfl⟩
      exact Subgroup.pow_mem _ hmem _
    · rw [Subgroup.closure_le]
      rintro y ⟨i, rfl⟩
      change B.b i.succ ∈ E ⊓ K
      exact ⟨by rw [← hspan]; exact B.b_mem_span i.succ,
        hbiK i.succ (Fin.succ_ne_zero i)⟩
  have hcentT : Subgroup.centralizer (T : Set G) ⊓ K = T := by
    change Subgroup.centralizer ((E ⊓ K : Subgroup G) : Set G) ⊓ K = E ⊓ K
    exact hcentA
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := by
    intro t ht
    change t ∈ E ⊓ K at ht
    exact hmaxA.2.1.2 t ht
  have hcolT : ∀ t ∈ T, s * t * s⁻¹ = s' * t * s'⁻¹ := by
    intro t ht
    rw [hTeq] at ht
    induction ht using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hcol i.succ
    | one => simp
    | mul x y hx hy ihx ihy =>
        calc s * (x * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
          _ = (s' * x * s'⁻¹) * (s' * y * s'⁻¹) := by rw [ihx, ihy]
          _ = s' * (x * y) * s'⁻¹ := by group
    | inv x hx ih =>
        calc s * x⁻¹ * s⁻¹ = (s * x * s⁻¹)⁻¹ := by group
          _ = (s' * x * s'⁻¹)⁻¹ := by rw [ih]
          _ = s' * x⁻¹ * s'⁻¹ := by group
  have key : ∀ (s₁ s₂ : G), s₁ ∈ K → s₂ ∈ K → s₁ * s₁ = 1 → s₂ * s₂ = 1 →
      s₁ * h * s₁⁻¹ = h⁻¹ →
      (∀ t ∈ E ⊓ K, ∀ x ∈ Subgroup.closure {B.vec v, s₁},
        t * x * t⁻¹ ∈ Subgroup.closure {B.vec v, s₁}) →
      (∀ t ∈ T, s₁ * t * s₁⁻¹ = s₂ * t * s₂⁻¹) →
      s₂ ∈ Subgroup.closure {B.vec v, s₁} := by
    intro s₁ s₂ hs₁ hs₂ hs₁2 hs₂2 hs₁h hNs hcomm
    have hgen₁ : Subgroup.closure ({B.vec v, s₁} : Set G) =
        Subgroup.closure ({h, s₁} : Set G) := by rw [← hhdef]
    have hs₁_inv : s₁⁻¹ = s₁ := inv_eq_of_mul_eq_one_right hs₁2
    have hs₂_inv : s₂⁻¹ = s₂ := inv_eq_of_mul_eq_one_right hs₂2
    let t : G := s₁ * s₂⁻¹
    have ht0C : s₂⁻¹ * s₁ ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have h := hcomm x hx
      calc x * (s₂⁻¹ * s₁) = s₂⁻¹ * (s₂ * x * s₂⁻¹) * s₁ := by group
        _ = s₂⁻¹ * (s₁ * x * s₁⁻¹) * s₁ := by rw [← h]
        _ = (s₂⁻¹ * s₁) * x := by group
    have ht0K : s₂⁻¹ * s₁ ∈ K := K.mul_mem (K.inv_mem hs₂) hs₁
    have ht0T : s₂⁻¹ * s₁ ∈ T := by
      rw [← hcentT]
      exact ⟨ht0C, ht0K⟩
    have htT : t ∈ T := by
      have hinv := T.inv_mem ht0T
      simpa [t, mul_inv_rev, hs₁_inv, hs₂_inv] using hinv
    have hxmem0 : t * s₁ * t⁻¹ ∈ Subgroup.closure ({B.vec v, s₁} : Set G) :=
      hNs t htT s₁ (Subgroup.subset_closure (by simp))
    have hxmem : t * s₁ * t⁻¹ ∈ Subgroup.closure ({h, s₁} : Set G) := by
      rwa [hgen₁] at hxmem0
    have hx2 : (t * s₁ * t⁻¹) * (t * s₁ * t⁻¹) = 1 := by
      calc (t * s₁ * t⁻¹) * (t * s₁ * t⁻¹) = t * (s₁ * s₁) * t⁻¹ := by group
        _ = 1 := by rw [hs₁2]; group
    rcases involution_mem_closure_pair h3 hs₁2 hs₁h hxmem hx2 with hx1 | ⟨i, hi⟩
    · exfalso
      have hs₁1 : s₁ = 1 := by
        have h : t⁻¹ * (t * s₁ * t⁻¹) * t = s₁ := by group
        rw [hx1] at h
        simpa using h.symm
      have hh1 : h = 1 := by
        have h2 : h = h⁻¹ := by
          rw [← hs₁h, hs₁1]
          group
        have hh2 : h * h = 1 := by
          have h' := congrArg (fun x => h * x) h2
          rwa [mul_inv_cancel] at h'
        have h3' : h ^ 2 * h = 1 := by rw [← pow_succ]; exact h3
        calc h = h ^ 2 * h := by rw [pow_two, hh2, one_mul]
          _ = 1 := h3'
      exact hhne hh1
    · have hst : s₁ * t * s₁⁻¹ = t⁻¹ := by
        have h2 : t = s₁ * s₂⁻¹ := rfl
        rw [h2, hs₁_inv, mul_inv_rev, inv_inv, hs₂_inv, hs₁_inv, ← mul_assoc, hs₁2,
          one_mul]
      have hconj := conj_eq_zpow_mul_of_conj_eq hs₁2 hi
      have hy_eq : h ^ (-i) = t := by
        have hprod : h ^ (-i) * t = t⁻¹ := hconj.symm.trans hst
        have h2 : h ^ (-i) = t⁻¹ * t⁻¹ := by
          calc h ^ (-i) = h ^ (-i) * t * t⁻¹ := by
                rw [mul_assoc, mul_inv_cancel, mul_one]
            _ = t⁻¹ * t⁻¹ := by rw [hprod]
        have ht3 : t ^ 3 = 1 := hTexp t htT
        have ht3' : t * t * t = 1 := by rw [← ht3, pow_succ, pow_two]
        have htinv : t⁻¹ = t * t := inv_eq_of_mul_eq_one_left ht3'
        have ht22 : t⁻¹ * t⁻¹ = t := by
          calc t⁻¹ * t⁻¹ = (t * t) * (t * t) := by rw [htinv]
            _ = t * (t * t * t) := by group
            _ = t * 1 := by rw [ht3']
            _ = t := mul_one t
        rw [h2, ht22]
      have ht_zpow : t ∈ Subgroup.zpowers h := by
        rw [← hy_eq]
        exact Subgroup.zpow_mem_zpowers h (-i)
      have hzle : Subgroup.zpowers h ≤ Subgroup.closure ({h, s₁} : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      have htinv_mem : t⁻¹ ∈ Subgroup.closure ({h, s₁} : Set G) :=
        hzle (Subgroup.inv_mem _ ht_zpow)
      have hs₂_eq : s₂ = t⁻¹ * s₁ := by
        have h2 : t = s₁ * s₂⁻¹ := rfl
        rw [h2, mul_inv_rev, inv_inv, hs₁_inv, mul_assoc, hs₁2, mul_one]
      have hs₂_mem : s₂ ∈ Subgroup.closure ({h, s₁} : Set G) := by
        rw [hs₂_eq]
        exact Subgroup.mul_mem _ htinv_mem (Subgroup.subset_closure (by simp))
      rwa [← hgen₁] at hs₂_mem
  have hS' : s' ∈ Subgroup.closure {B.vec v, s} :=
    key s s' hs hs' hs2 hs'2 hsh hN hcolT
  have hS : s ∈ Subgroup.closure {B.vec v, s'} :=
    key s' s hs' hs hs'2 hs2 hsh' hN' (fun t ht => (hcolT t ht).symm)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]
      exact Subgroup.subset_closure (by simp)
    · rw [hx]
      exact hS
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [hx]
      exact Subgroup.subset_closure (by simp)
    · rw [hx]
      exact hS'

end CFSG.StandardType.FrameRoute.FS81

end
