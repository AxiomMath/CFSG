module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.Inputs
public import CFSG.Quasithin.EmptyFaithful.SzF53MZa

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open Equiv

private theorem c4_sq_ne_one : F53.c4 ^ 2 ≠ 1 := by decide +kernel

private theorem c4_mem_D0fin : F53.c4 ∈ F53.D0fin := by decide +kernel

open scoped Pointwise in
theorem card_le_four_of_sq_eq_one {B : Subgroup (Perm (Fin 5))} (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card B ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by simpa using hB x x.2)⟩
  obtain ⟨hD2, hDs, -⟩ := F53.sylow_of_card_eight F53.D0 F53.D0_card
  obtain ⟨P, hBP⟩ := hB2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hD2.toSylow hDs) P
  have hPeq : (P : Subgroup (Perm (Fin 5))) = MulAut.conj g • F53.D0 := by
    have := congrArg (fun Q : Sylow 2 (Perm (Fin 5)) => (Q : Subgroup (Perm (Fin 5)))) hg
    simpa [Sylow.coe_subgroup_smul] using this.symm
  set B' : Subgroup (Perm (Fin 5)) := B.map (MulAut.conj g⁻¹).toMonoidHom with hB'
  have hcard : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hB'D : B' ≤ F53.D0 := by
    rintro _ ⟨b, hb, rfl⟩
    have hbP : b ∈ MulAut.conj g • F53.D0 := hPeq ▸ hBP hb
    rw [Subgroup.mem_smul_pointwise_iff_exists] at hbP
    obtain ⟨y, hy, rfl⟩ := hbP
    simpa [MulAut.conj_apply, mul_assoc] using hy
  have hdvd : Nat.card B' ∣ 8 := F53.D0_card ▸ Subgroup.card_dvd_of_le hB'D
  have hne : Nat.card B' ≠ 8 := by
    intro h8
    have hBeq : B' = F53.D0 :=
      Subgroup.eq_of_le_of_card_ge hB'D (by rw [h8, F53.D0_card])
    have hmem : F53.c4 ∈ B' := by rw [hBeq]; exact c4_mem_D0fin
    obtain ⟨b, hb, hbc⟩ := hmem
    apply c4_sq_ne_one
    rw [← hbc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_pow, hB b hb]
    group
  have hle : Nat.card B' ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  rw [← hcard]
  interval_cases h : Nat.card B' <;> omega

set_option synthInstance.maxSize 1000 in
private theorem partner_dec : ∀ σ : Perm (Fin 5), σ ≠ 1 → σ ^ 2 = 1 → Perm.sign σ ≠ 1 →
    ∀ ρ : Perm (Fin 5), ρ ≠ 1 → ρ ≠ σ → ρ ^ 2 = 1 → ρ * σ = σ * ρ →
      (ρ ≠ 1 ∧ ρ ^ 2 = 1 ∧ Perm.sign ρ ≠ 1 ∧ ρ ≠ σ ∧
          σ * ρ ≠ 1 ∧ (σ * ρ) ^ 2 = 1 ∧ Perm.sign (σ * ρ) = 1) ∨
        (σ * ρ ≠ 1 ∧ (σ * ρ) ^ 2 = 1 ∧ Perm.sign (σ * ρ) ≠ 1 ∧ σ * ρ ≠ σ ∧
          σ * (σ * ρ) ≠ 1 ∧ (σ * (σ * ρ)) ^ 2 = 1 ∧ Perm.sign (σ * (σ * ρ)) = 1) := by
  decide +kernel

theorem isSwap_of_idx_orth_le_two {σ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : idx orth σ ≤ 2) :
    σ.IsSwap := by
  rw [idx_orth] at h2
  simp only [h1, ↓reduceIte] at h2
  rw [isSwap_iff]
  refine ⟨h1, ?_⟩
  by_cases hs : σ ^ 2 = 1
  · by_cases hg : Perm.sign σ = 1
    · simp [hs, hg] at h2
    · exact ⟨hs, hg⟩
  · exfalso
    simp only [hs, ↓reduceIte] at h2
    split_ifs at h2 <;> omega

theorem idx_orth_eq_four {σ : Perm (Fin 5)} (h1 : σ ≠ 1) (h2 : σ ^ 2 = 1)
    (h3 : Perm.sign σ = 1) : idx orth σ = 4 := by
  rw [idx_orth]
  simp [h1, h2, h3]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_quotHom_five {X : Subgroup G} (hX : Nonempty (OTwoQuot X ≃* Perm (Fin 5))) :
    ∃ ψ : ↥X →* Perm (Fin 5), Function.Surjective ψ ∧ ψ.ker = (pCoreOf 2 X).subgroupOf X := by
  obtain ⟨e⟩ := hX
  refine ⟨(e : OTwoQuot X →* Perm (Fin 5)).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X)),
    fun p => ?_, ?_⟩
  · obtain ⟨q, rfl⟩ := e.surjective p
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨x, rfl⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe]

omit [Finite G] in
theorem relIndex_inf_eq_card_map {K : Type*} [Group K] {X A N : Subgroup G} {ψ : ↥X →* K}
    (hψ : ψ.ker = N.subgroupOf X) (hAX : A ≤ X) :
    (A ⊓ N).relIndex A = Nat.card ((A.subgroupOf X).map ψ) := by
  rw [← Subgroup.relIndex_ker, hψ, Subgroup.relIndex_subgroupOf hAX,
    Subgroup.inf_relIndex_left]

omit [Finite G] in
theorem relIndex_le_four_of_elemAbelian {X A : Subgroup G}
    (hX : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) (hAX : A ≤ X) (hA : IsElemAbelian 2 A) :
    (A ⊓ pCoreOf 2 X).relIndex A ≤ 4 := by
  obtain ⟨ψ, -, hψ⟩ := exists_quotHom_five hX
  rw [relIndex_inf_eq_card_map hψ hAX]
  apply card_le_four_of_sq_eq_one
  rintro _ ⟨a, ha, rfl⟩
  have ha2 : a ^ 2 = 1 := Subtype.ext (hA.2 _ (Subgroup.mem_subgroupOf.mp ha))
  rw [← map_pow, ha2, map_one]

private theorem relIndex_ne_zero' (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  (H.subgroupOf K).index_ne_zero_of_finite

theorem idx_le_relIndex_centralizer {n : ℕ} {M : Model n} {X L V : Subgroup G}
    [(L.subgroupOf V).Normal] {θ : ↥X →* Perm (Fin n)} {β : M.W →* ↥V ⧸ L.subgroupOf V}
    (hsd : SecData M X L V θ β) (hLV : L ≤ V) {x : G} (hx : x ∈ X) :
    idx M (θ ⟨x, hx⟩) ≤ (V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex V := by
  rw [← hsd.secIdx_eq_idx hLV hx]
  unfold secIdx
  refine Subgroup.relIndex_le_of_le_left ?_ (relIndex_ne_zero' _ _)
  intro v hv
  obtain ⟨hvV, hvx⟩ := Subgroup.mem_inf.mp hv
  have hc : Commute v x := Subgroup.mem_centralizer_singleton_iff.mp hvx
  unfold fixSecIn
  refine Subgroup.subset_closure ⟨hvV, fun a ha => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [comm_eq_one_iff.mpr (hc.zpow_right k).symm.eq]
  exact L.one_mem

omit [Finite G] in
theorem relIndex_centralizer_conj {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (s : G) :
    (V ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set G)).relIndex V =
      (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V := by
  set f : G →* G := (MulAut.conj g).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj g).injective
  have hfx : ∀ x, f x = g * x * g⁻¹ := fun x => rfl
  have hginv : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hg
  have hV : V.map f = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hfx]
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    · intro hx
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hginv x).mp hx
        simpa using this
      · rw [hfx]; group
  have hC : (V ⊓ Subgroup.centralizer ({s} : Set G)).map f =
      V ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyV, hys⟩ := Subgroup.mem_inf.mp hy
      rw [hfx]
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyV, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Commute.conj (Subgroup.mem_centralizer_singleton_iff.mp hys) g)
    · intro hx
      obtain ⟨hxV, hxs⟩ := Subgroup.mem_inf.mp hx
      refine ⟨g⁻¹ * x * g, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp hginv x).mp hxV
        simpa using this
      · have hc : Commute x (g * s * g⁻¹) := Subgroup.mem_centralizer_singleton_iff.mp hxs
        have e : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        rw [e] at hc
        exact Subgroup.mem_centralizer_singleton_iff.mpr ((Commute.conj_iff g).mp hc)
      · rw [hfx]; group
  calc (V ⊓ Subgroup.centralizer ({g * s * g⁻¹} : Set G)).relIndex V
      = ((V ⊓ Subgroup.centralizer ({s} : Set G)).map f).relIndex (V.map f) := by rw [hC, hV]
    _ = (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V :=
      Subgroup.relIndex_map_map_of_injective _ _ hfinj

theorem exists_partner (h15 : Hss15) {X V A : Subgroup G}
    (hX : Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5))) (hVQ : V ≤ pCoreOf 2 X)
    (hVn : X ≤ Subgroup.normalizer (V : Set G)) (hV : IsElemAbelian 2 V)
    (hC : X ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X)
    {s : G} (hs : s ∈ A) (hsV : (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V = 2)
    (hAX : A ≤ X) (hA : IsElemAbelian 2 A) (hAi : (A ⊓ pCoreOf 2 X).relIndex A = 4) :
    ∃ u ∈ A, A ≤ Subgroup.closure {s, u} ⊔ (A ⊓ pCoreOf 2 X) ∧
      ¬ (V ⊓ Subgroup.centralizer ({u} : Set G) ≤ V ⊓ Subgroup.centralizer ({s} : Set G)) := by
  have hsX : s ∈ X := hAX hs
  have horth : IsOrthSec X (V ⊓ Subgroup.centralizer (X : Set G)) V :=
    h15 G X V hX hVQ hVn hV hC s hsX hsV
  have hcs := IsModelSec.cSecIn_eq_pCoreOf horth hX
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := horth
  rw [hcs] at hθk
  have hLV : V ⊓ Subgroup.centralizer (X : Set G) ≤ V := inf_le_left
  have hidx : ∀ {x : G} (hx : x ∈ X),
      idx orth (θ ⟨x, hx⟩) ≤ (V ⊓ Subgroup.centralizer ({x} : Set G)).relIndex V :=
    fun hx => idx_le_relIndex_centralizer hsd hLV hx
  have hker : ∀ x : ↥X, θ x = 1 ↔ (x : G) ∈ pCoreOf 2 X := fun x => by
    rw [← MonoidHom.mem_ker, hθk, Subgroup.mem_subgroupOf]
  have hQV : ∀ q ∈ pCoreOf 2 X, ∀ v ∈ V, Commute v q := by
    intro q hq v hv
    have hq' : q ∈ X ⊓ Subgroup.centralizer (V : Set G) := by rw [hC]; exact hq
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hq').2 v hv
  obtain ⟨σ, hσ⟩ : ∃ σ, θ ⟨s, hsX⟩ = σ := ⟨_, rfl⟩
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hsQ : s ∈ pCoreOf 2 X := (hker ⟨s, hsX⟩).mp (hσ.trans h1)
    have : (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V = 1 := by
      rw [Subgroup.relIndex_eq_one]
      intro v hv
      exact Subgroup.mem_inf.mpr ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr (hQV s hsQ v hv)⟩
    omega
  have hσswap : σ.IsSwap := by
    have h := hidx hsX
    rw [hσ, hsV] at h
    exact isSwap_of_idx_orth_le_two hσ1 h
  obtain ⟨-, hσ2, hσsg⟩ := (isSwap_iff σ).mp hσswap
  have hzσ : ∀ τ, τ ∈ Subgroup.zpowers σ ↔ τ = 1 ∨ τ = σ := by
    intro τ
    rw [mem_zpowers_iff_of_pow_eq_one hσ2 (by norm_num)]
    constructor
    · rintro ⟨k, hk, rfl⟩
      interval_cases k <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, pow_zero _⟩
      · exact ⟨1, by norm_num, pow_one _⟩
  have hcardσ : Nat.card (Subgroup.zpowers σ) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime hσ2 hσ1]
  set Abar := (A.subgroupOf X).map θ with hAbar
  have hAbar4 : Nat.card Abar = 4 := by rw [← relIndex_inf_eq_card_map hθk hAX, hAi]
  obtain ⟨ρ, hρA, hρσ⟩ : ∃ ρ ∈ Abar, ρ ∉ Subgroup.zpowers σ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show Abar ≤ Subgroup.zpowers σ from hcon)
    omega
  obtain ⟨⟨a₀, ha₀X⟩, ha₀, rfl⟩ := hρA
  have ha₀A : a₀ ∈ A := Subgroup.mem_subgroupOf.mp ha₀
  have hρ1 : θ ⟨a₀, ha₀X⟩ ≠ 1 := fun h => hρσ ((hzσ _).mpr (Or.inl h))
  have hρσ' : θ ⟨a₀, ha₀X⟩ ≠ σ := fun h => hρσ ((hzσ _).mpr (Or.inr h))
  have hρ2 : θ ⟨a₀, ha₀X⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨a₀, ha₀X⟩ : ↥X) ^ 2 = 1 := Subtype.ext (hA.2 a₀ ha₀A)
    rw [this, map_one]
  have hρc : θ ⟨a₀, ha₀X⟩ * σ = σ * θ ⟨a₀, ha₀X⟩ := by
    have hcomm : a₀ * s = s * a₀ :=
      congrArg Subtype.val (isMulCommutative_iff.mp hA.1 ⟨a₀, ha₀A⟩ ⟨s, hs⟩)
    rw [← hσ, ← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext hcomm)
  obtain ⟨u, huA, hτprop⟩ : ∃ u, ∃ huA : u ∈ A,
      θ ⟨u, hAX huA⟩ ≠ 1 ∧ θ ⟨u, hAX huA⟩ ^ 2 = 1 ∧ Perm.sign (θ ⟨u, hAX huA⟩) ≠ 1 ∧
        θ ⟨u, hAX huA⟩ ≠ σ ∧ σ * θ ⟨u, hAX huA⟩ ≠ 1 ∧ (σ * θ ⟨u, hAX huA⟩) ^ 2 = 1 ∧
        Perm.sign (σ * θ ⟨u, hAX huA⟩) = 1 := by
    rcases partner_dec σ hσ1 hσ2 hσsg _ hρ1 hρσ' hρ2 hρc with h | h
    · exact ⟨a₀, ha₀A, h⟩
    · refine ⟨s * a₀, A.mul_mem hs ha₀A, ?_⟩
      have e : θ ⟨s * a₀, hAX (A.mul_mem hs ha₀A)⟩ = σ * θ ⟨a₀, ha₀X⟩ := by
        rw [← hσ, ← map_mul]; rfl
      rw [e]
      exact h
  have huX : u ∈ X := hAX huA
  obtain ⟨τ, hτ⟩ : ∃ τ, θ ⟨u, huX⟩ = τ := ⟨_, rfl⟩
  rw [hτ] at hτprop
  obtain ⟨hτ1, hτ2, hτsg, hτσ, hστ1, hστ2, hστsg⟩ := hτprop
  have hτz : τ ∉ Subgroup.zpowers σ := by
    rw [hzσ]
    rintro (h | h)
    · exact hτ1 h
    · exact hτσ h
  have hτswap : τ.IsSwap := (isSwap_iff τ).mpr ⟨hτ1, hτ2, hτsg⟩
  have hστ4 : idx orth (σ * τ) = 4 := idx_orth_eq_four hστ1 hστ2 hστsg
  refine ⟨u, huA, ?_, ?_⟩
  ·
    set D := Subgroup.closure ({s, u} : Set G) with hD
    have hDA : D ≤ A := by
      rw [hD, Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hs
      · exact huA
    set Dbar := (D.subgroupOf X).map θ with hDbar
    have hDbarA : Dbar ≤ Abar := Subgroup.map_mono fun x hx => hDA hx
    have hσD : σ ∈ Dbar :=
      ⟨⟨s, hsX⟩, Subgroup.subset_closure (Set.mem_insert s _), hσ⟩
    have hτD : τ ∈ Dbar :=
      ⟨⟨u, huX⟩, Subgroup.subset_closure (Set.mem_insert_of_mem s rfl), hτ⟩
    have hzD : Subgroup.zpowers σ ≤ Dbar := (Subgroup.zpowers_le).mpr hσD
    have hDbarEq : Dbar = Abar := by
      apply Subgroup.eq_of_le_of_card_ge hDbarA
      rw [hAbar4]
      have h1 : Nat.card Dbar ∣ 4 := hAbar4 ▸ Subgroup.card_dvd_of_le hDbarA
      have h2 : 2 ∣ Nat.card Dbar := hcardσ ▸ Subgroup.card_dvd_of_le hzD
      have h3 : Nat.card Dbar ≠ 2 := by
        intro h
        have : Subgroup.zpowers σ = Dbar :=
          Subgroup.eq_of_le_of_card_ge hzD (by rw [h, hcardσ])
        exact hτz (this ▸ hτD)
      have h4 : Nat.card Dbar ≤ 4 := Nat.le_of_dvd (by norm_num) h1
      interval_cases h : Nat.card Dbar <;> omega
    intro a ha
    have haX : a ∈ X := hAX ha
    have haD : θ ⟨a, haX⟩ ∈ Dbar := hDbarEq ▸ (⟨⟨a, haX⟩, ha, rfl⟩ : θ ⟨a, haX⟩ ∈ Abar)
    obtain ⟨d, hd, hda⟩ := haD
    have hdD : (d : G) ∈ D := hd
    have hq : (d : G)⁻¹ * a ∈ pCoreOf 2 X := by
      have h1 : θ (d⁻¹ * ⟨a, haX⟩) = 1 := by rw [map_mul, map_inv, hda, inv_mul_cancel]
      exact (hker _).mp h1
    have hqA : (d : G)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem (hDA hdD)) ha
    have e : a = (d : G) * ((d : G)⁻¹ * a) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hdD (Subgroup.mem_inf.mpr ⟨hqA, hq⟩)
  ·
    intro hle
    obtain ⟨i, j, hij, hσij⟩ := hσswap
    obtain ⟨k, l, hkl, hτkl⟩ := hτswap
    have hconj : IsConj σ τ := by
      rw [hσij, hτkl]
      exact Equiv.Perm.isConj_swap hij hkl
    obtain ⟨π, hπ⟩ := isConj_iff.mp hconj
    obtain ⟨g, rfl⟩ := hθs π
    have htX : (g : G) * s * (g : G)⁻¹ ∈ X := X.mul_mem (X.mul_mem g.2 hsX) (X.inv_mem g.2)
    have hθt : θ ⟨(g : G) * s * (g : G)⁻¹, htX⟩ = τ := by
      rw [← hπ, ← hσ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hq : ((g : G) * s * (g : G)⁻¹)⁻¹ * u ∈ pCoreOf 2 X := by
      have h1 : θ ((⟨(g : G) * s * (g : G)⁻¹, htX⟩ : ↥X)⁻¹ * ⟨u, huX⟩) = 1 := by
        rw [map_mul, map_inv, hθt, hτ, inv_mul_cancel]
      exact (hker _).mp h1
    have htu : V ⊓ Subgroup.centralizer ({(g : G) * s * (g : G)⁻¹} : Set G) ≤
        V ⊓ Subgroup.centralizer ({u} : Set G) := by
      intro v hv
      obtain ⟨hvV, hvt⟩ := Subgroup.mem_inf.mp hv
      refine Subgroup.mem_inf.mpr ⟨hvV, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := Commute.mul_right (Subgroup.mem_centralizer_singleton_iff.mp hvt)
        (hQV _ hq v hvV)
      rwa [mul_inv_cancel_left] at h1
    have hu2 : (V ⊓ Subgroup.centralizer ({u} : Set G)).relIndex V ≤ 2 := by
      calc (V ⊓ Subgroup.centralizer ({u} : Set G)).relIndex V
          ≤ (V ⊓ Subgroup.centralizer ({(g : G) * s * (g : G)⁻¹} : Set G)).relIndex V :=
            Subgroup.relIndex_le_of_le_left htu (relIndex_ne_zero' _ _)
        _ = (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V :=
            relIndex_centralizer_conj (hVn g.2) s
        _ = 2 := hsV
    have hsu : V ⊓ Subgroup.centralizer ({u} : Set G) ≤
        V ⊓ Subgroup.centralizer ({s * u} : Set G) := by
      intro v hv
      obtain ⟨hvV, hvu⟩ := Subgroup.mem_inf.mp hv
      obtain ⟨-, hvs⟩ := Subgroup.mem_inf.mp (hle hv)
      refine Subgroup.mem_inf.mpr ⟨hvV, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      exact Commute.mul_right (Subgroup.mem_centralizer_singleton_iff.mp hvs)
        (Subgroup.mem_centralizer_singleton_iff.mp hvu)
    have hsuX : s * u ∈ X := X.mul_mem hsX huX
    have h4 : idx orth (θ ⟨s * u, hsuX⟩) ≤ 2 :=
      (hidx hsuX).trans ((Subgroup.relIndex_le_of_le_left hsu (relIndex_ne_zero' _ _)).trans hu2)
    have e : θ ⟨s * u, hsuX⟩ = σ * τ := by
      rw [← hσ, ← hτ, ← map_mul]; rfl
    rw [e, hστ4] at h4
    omega

end F53.Stellmacher

end CFSG.Quasithin
