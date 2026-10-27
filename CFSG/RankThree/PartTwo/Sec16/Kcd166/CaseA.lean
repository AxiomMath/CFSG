module

public import CFSG.RankThree.PartTwo.Sec16.Kcd166.PermDegNine
public import CFSG.Walter.ReeOrder.JT.AuxWeights
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalPGroupSimpleModule
public import CFSG.RankThree.PartTwo.Sec16.Item166ThetaTripleA6
public import CFSG.GroupTheory.PerfectCentralExtensionUnique

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG CFSG.RankThree.PartTwo

private noncomputable def normalizerHom {Γ : Type*} [Group Γ] {Q : Subgroup Γ} [Q.Normal] :
    Γ →* Subgroup.normalizer (Q : Set Γ) where
  toFun g := ⟨g, by
    rw [Subgroup.normalizer_eq_top (H := Q)]
    exact Subgroup.mem_top g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma weightSpace_map_eq_twist {K V Γ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Group Γ] (ρ : Representation K Γ V) (N : Subgroup Γ)
    (g : Subgroup.normalizer (N : Set Γ)) (χ : N → K) :
    (CFSG.Walter.JT.weightSpace ρ N χ).map (ρ g) =
      CFSG.Walter.JT.weightSpace ρ N (CFSG.Walter.JT.twist g χ) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro v hv
    exact CFSG.Walter.JT.map_mem_weightSpace_twist (ρ := ρ) g hv
  · intro v hv
    refine ⟨ρ (g⁻¹) v, ?_, ?_⟩
    · have h := CFSG.Walter.JT.map_mem_weightSpace_twist (ρ := ρ) (g⁻¹) hv
      rwa [← CFSG.Walter.JT.twist_mul, inv_mul_cancel,
        CFSG.Walter.JT.twist_one] at h
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]

private lemma iSup_weightSpace_eq_iSup_weights {K V Γ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Group Γ] (ρ : Representation K Γ V) (N : Subgroup Γ) :
    (⨆ χ : CFSG.Walter.JT.weights ρ N, CFSG.Walter.JT.weightSpace ρ N χ) =
      ⨆ χ : N → K, CFSG.Walter.JT.weightSpace ρ N χ := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun χ => ?_
    exact le_iSup (fun χ : N → K => CFSG.Walter.JT.weightSpace ρ N χ) χ.1
  · refine iSup_le fun χ => ?_
    by_cases h : CFSG.Walter.JT.weightSpace ρ N χ = ⊥
    · rw [h]
      exact bot_le
    · exact le_iSup (fun χ' : CFSG.Walter.JT.weights ρ N =>
        CFSG.Walter.JT.weightSpace ρ N χ') ⟨χ, h⟩

private noncomputable def weightHom {K V Γ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Group Γ] (ρ : Representation K Γ V) (Q : Subgroup Γ) [Q.Normal] :
    Γ →* Equiv.Perm (CFSG.Walter.JT.weights ρ Q) :=
  (CFSG.Walter.JT.weightPerm ρ Q).comp (normalizerHom (Q := Q))

private lemma weightSpace_map_weightHom {K V Γ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Group Γ] (ρ : Representation K Γ V) (Q : Subgroup Γ) [Q.Normal]
    (g : Γ) (χ : CFSG.Walter.JT.weights ρ Q) :
    (CFSG.Walter.JT.weightSpace ρ Q χ).map (ρ g) =
      CFSG.Walter.JT.weightSpace ρ Q (weightHom ρ Q g χ) := by
  change (CFSG.Walter.JT.weightSpace ρ Q χ).map (ρ (normalizerHom (Q := Q) g)) =
    CFSG.Walter.JT.weightSpace ρ Q (weightHom ρ Q g χ)
  rw [weightSpace_map_eq_twist ρ Q (normalizerHom (Q := Q) g) χ]
  congr 1

private lemma nontrivial_of_isIrreducible {K V Γ : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Group Γ] {ρ : Representation K Γ V} (hirr : ρ.IsIrreducible) :
    Nontrivial V := by
  haveI : IsSimpleModule (MonoidAlgebra K Γ) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra K Γ) ρ.asModule
  exact ρ.asModuleEquiv.symm.toEquiv.nontrivial

private lemma weightAction_orbit_eq_top {K V Γ Ω : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Group Γ] {ρ : Representation K Γ V} (hirr : ρ.IsIrreducible)
    (W : Ω → Submodule K V) (σ : Γ →* Equiv.Perm Ω)
    (hmap : ∀ g χ, (W χ).map (ρ g) = W (σ g χ))
    (χ₀ : Ω) (hWne : W χ₀ ≠ ⊥) :
    (⨆ x : Set.range fun g : Γ => σ g χ₀, W x.1) = ⊤ := by
  classical
  letI : ρ.IsIrreducible := hirr
  let S : Set Ω := Set.range fun g : Γ => σ g χ₀
  let U : Submodule K V := ⨆ x : S, W x.1
  have hUle (g : Γ) : U ≤ U.comap (ρ g) := by
    refine iSup_le fun x => ?_
    intro v hv
    rw [Submodule.mem_comap]
    obtain ⟨h, hx⟩ := x.2
    have hv' : ρ g v ∈ W (σ g x.1) := by
      rw [← hmap g x.1]
      exact ⟨v, hv, rfl⟩
    have hEq : σ g x.1 = σ (g * h) χ₀ := by
      rw [← hx, map_mul]
      rfl
    rw [hEq] at hv'
    exact le_iSup (fun x : S => W x.1)
      (⟨σ (g * h) χ₀, ⟨g * h, rfl⟩⟩ : S) hv'
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hle : W χ₀ ≤ U := by
      simpa using (le_iSup (fun x : S => W x.1) ⟨χ₀, ⟨1, by simp⟩⟩)
    rw [hbot] at hle
    exact hWne (le_bot_iff.mp hle)
  let Urep : Subrepresentation ρ :=
    { toSubmodule := U
      apply_mem_toSubmodule := fun g v hv => by
        have h := hUle g hv
        rwa [Submodule.mem_comap] at h }
  have hUrepne : Urep ≠ ⊥ := by
    intro h
    apply hUne
    ext v
    have hv : v ∈ Urep ↔ v ∈ (⊥ : Subrepresentation ρ) := by rw [h]
    exact hv
  have hUreptop : Urep = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top Urep).resolve_left hUrepne
  have hUtop : U = ⊤ := by
    ext v
    have hv : v ∈ Urep ↔ v ∈ (⊤ : Subrepresentation ρ) := by rw [hUreptop]
    exact hv
  simpa [S, U] using hUtop

private lemma transitive_of_weightAction {K V Γ Ω : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Group Γ] {ρ : Representation K Γ V} (hirr : ρ.IsIrreducible)
    (W : Ω → Submodule K V) (σ : Γ →* Equiv.Perm Ω)
    (hmap : ∀ g χ, (W χ).map (ρ g) = W (σ g χ))
    (hind : iSupIndep W) (htop : ⨆ χ, W χ = ⊤)
    (hWne : ∀ χ, W χ ≠ ⊥) (χ₀ : Ω) :
    ∀ ψ : Ω, ∃ g : Γ, σ g χ₀ = ψ := by
  classical
  let S : Set Ω := Set.range fun g : Γ => σ g χ₀
  have hUtop : (⨆ x : S, W x.1) = ⊤ :=
    weightAction_orbit_eq_top hirr W σ hmap χ₀ (hWne χ₀)
  have hSuniv : S = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ψ
    by_contra hψ
    have hdisj : Disjoint (W ψ) (⨆ x ∈ S, W x) := hind.disjoint_biSup hψ
    have hdisj' : Disjoint (W ψ) (⨆ x : S, W x.1) := by
      simpa only [iSup_subtype''] using hdisj
    have hle : W ψ ≤ (⨆ x : S, W x.1) := by
      rw [hUtop]
      exact le_top
    exact hWne ψ (hdisj'.eq_bot_of_le hle)
  intro ψ
  have hmem : ψ ∈ S := by rw [hSuniv]; trivial
  exact hmem

private lemma exists_smul_eq_of_isPretransitive {Γ Ω : Type*} [Group Γ]
    (σ : Γ →* Equiv.Perm Ω) (htrans : MulAction.IsPretransitive σ.range Ω)
    (χ ψ : Ω) : ∃ g : Γ, σ g χ = ψ := by
  obtain ⟨p, hp⟩ := htrans.exists_smul_eq χ ψ
  obtain ⟨g, hg⟩ := p.2
  exact ⟨g, by rw [hg]; exact hp⟩

private lemma eq_bot_of_isPGroup_of_charP {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (hp : p.Prime) {Γ : Type*} [Group Γ] [Finite Γ] {V : Type*} [AddCommGroup V]
    [Module K V]
    {ρ : Representation K Γ V} (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    {r : ℕ} {Q : Subgroup Γ} (hQn : Q.Normal) (hQr : IsPGroup r Q) (hrp : r = p) :
    Q = ⊥ := by
  letI : Q.Normal := hQn
  letI : Fact p.Prime := ⟨hp⟩
  letI : ρ.IsIrreducible := hirr
  have hQrp : IsPGroup p Q := hrp ▸ hQr
  have hact := CFSG.TwoRankLowerBound.Helpers.normal_p_subgroup_irreducible_action_trivial
    p ρ Q hQrp
  rw [eq_bot_iff]
  intro q hq
  have hq1 : (⟨q, hq⟩ : Q) = 1 := by
    apply Subtype.ext
    apply hfaith
    simpa using hact ⟨q, hq⟩
  simpa using congrArg Subtype.val hq1

private lemma r_ne_p {K : Type*} [Field K] {p : ℕ} [CharP K p] (hp : p.Prime)
    {Γ : Type*} [Group Γ] [Finite Γ] {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K Γ V} (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    {r : ℕ} {Q : Subgroup Γ} (hQn : Q.Normal) (hQr : IsPGroup r Q)
    (hQZ : ¬ Q ≤ Subgroup.center Γ) (hrp : r = p) : False := by
  have hbot := eq_bot_of_isPGroup_of_charP hp hirr hfaith hQn hQr hrp
  exact hQZ (by rw [hbot]; exact bot_le)

private lemma card_Q_cast_ne_zero {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (hp : p.Prime) {r : ℕ} (hr : r.Prime) {Γ : Type*} [Group Γ] [Finite Γ]
    {Q : Subgroup Γ} (hQr : IsPGroup r Q) (hQZ : ¬ Q ≤ Subgroup.center Γ)
    (hrp : r ≠ p) : ((Nat.card Q : ℕ) : K) ≠ 0 := by
  letI : Fact r.Prime := ⟨hr⟩
  intro h0
  have hQne : Q ≠ ⊥ := fun h => hQZ (by rw [h]; exact bot_le)
  haveI : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQne
  have hpdvd : p ∣ Nat.card Q := (CharP.cast_eq_zero_iff K p (Nat.card Q)).mp h0
  obtain ⟨n, hn⟩ := hQr.exists_card_eq
  have hnpos : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have hsub : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hn).1
    exact false_of_nontrivial_of_subsingleton Q
  have hpr : p ∣ r := hp.dvd_of_dvd_pow (by rwa [hn] at hpdvd)
  exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp hpr).symm

private lemma eq_smul_one_of_subsingleton_weights {K V Γ : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Group Γ] {ρ : Representation K Γ V}
    {Q : Subgroup Γ} [Q.Normal]
    (htop : ⨆ χ : CFSG.Walter.JT.weights ρ Q,
      CFSG.Walter.JT.weightSpace ρ Q χ = ⊤)
    [Subsingleton (CFSG.Walter.JT.weights ρ Q)]
    (χ₀ : CFSG.Walter.JT.weights ρ Q) :
    ∀ q : Q, ρ (q : Γ) = (χ₀.1 q) • 1 := by
  classical
  let Ω := CFSG.Walter.JT.weights ρ Q
  let W : Ω → Submodule K V := fun χ => CFSG.Walter.JT.weightSpace ρ Q χ
  have htop' : ⨆ χ : Ω, W χ = ⊤ := htop
  have hWtop : W χ₀ = ⊤ := by
    rw [← htop']
    refine le_antisymm (le_iSup W χ₀) (iSup_le fun χ => ?_)
    rw [Subsingleton.elim χ χ₀]
  intro q
  ext v
  have hv : v ∈ CFSG.Walter.JT.weightSpace ρ Q χ₀ := by
    rw [show CFSG.Walter.JT.weightSpace ρ Q χ₀ = W χ₀ from rfl, hWtop]
    exact Submodule.mem_top
  rw [CFSG.Walter.JT.mem_weightSpace] at hv
  simpa using hv q

private lemma two_le_card_weights {K V Γ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] [Group Γ] [Finite Γ] {ρ : Representation K Γ V}
    {Q : Subgroup Γ} [Q.Normal] [Finite (CFSG.Walter.JT.weights ρ Q)]
    (hfaith : Function.Injective ρ)
    (htop : ⨆ χ : CFSG.Walter.JT.weights ρ Q,
      CFSG.Walter.JT.weightSpace ρ Q χ = ⊤)
    (hQZ : ¬ Q ≤ Subgroup.center Γ) :
    2 ≤ Nat.card (CFSG.Walter.JT.weights ρ Q) := by
  classical
  let Ω := CFSG.Walter.JT.weights ρ Q
  let W : Ω → Submodule K V := fun χ => CFSG.Walter.JT.weightSpace ρ Q χ
  letI : Finite Ω := ‹Finite (CFSG.Walter.JT.weights ρ Q)›
  change 2 ≤ Nat.card Ω
  have htop' : ⨆ χ : Ω, W χ = ⊤ := htop
  have hne : Nonempty Ω := by
    by_contra h
    haveI : IsEmpty Ω := not_nonempty_iff.mp h
    have hbot : (⨆ χ : Ω, W χ) = ⊥ := iSup_of_empty W
    rw [htop'] at hbot
    exact bot_ne_top hbot.symm
  obtain ⟨χ₀⟩ := hne
  letI : Nonempty Ω := ⟨χ₀⟩
  by_contra hlt
  have hcard : Nat.card Ω = 1 := by
    have hpos : 0 < Nat.card Ω := Nat.card_pos
    omega
  obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hcard
  letI : Subsingleton Ω := hsub
  have hscalar : ∀ q : Q, ρ (q : Γ) = (χ₀.1 q) • 1 :=
    eq_smul_one_of_subsingleton_weights htop χ₀
  have hcomm (q : Q) (g : Γ) : (q : Γ) * g = g * q := by
    apply hfaith
    calc
      ρ ((q : Γ) * g) = ρ (q : Γ) * ρ g := map_mul ρ _ _
      _ = ((χ₀.1 q) • 1) * ρ g := by rw [hscalar q]
      _ = (χ₀.1 q) • ρ g := by simp
      _ = ρ g * ((χ₀.1 q) • 1) := by simp
      _ = ρ g * ρ (q : Γ) := by rw [hscalar q]
      _ = ρ (g * q) := by rw [map_mul]
  apply hQZ
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro g
  exact (hcomm ⟨q, hq⟩ g).symm

private lemma ker_comp_sigma_isSolvable {Y : Type*} {T : Type} [Group Y] [Group T]
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (π : Y →* T)
    (hK : Group.IsSolvable π.ker) :
    Group.IsSolvable
      ((CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker := by
  let σT := CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover hT
  have hσTker : σT.ker = Subgroup.center T :=
    CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover_ker hT
  haveI : Group.IsSolvable π.ker := hK
  set N : Subgroup Y := (Subgroup.center T).comap π
  have hker : ((σT).comp π).ker = N := by
    rw [← MonoidHom.comap_ker σT π, hσTker]
  have hle : π.ker ≤ N := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact Subgroup.one_mem _
  rw [hker]
  let f : π.ker →* N := Subgroup.inclusion hle
  let g : N →* Subgroup.center T := (π.comp N.subtype).codRestrict _ fun x => x.2
  have hfg : g.ker ≤ f.range := by
    intro x hx
    have h1 : π (x : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact ⟨⟨(x : Y), h1⟩, rfl⟩
  exact Group.isSolvable_of_ker_le_range f g hfg

private lemma false_of_ker_sup_ker_eq_top {Γ T Ω : Type*} [Group Γ] [Group T] [Fintype Ω]
    (π : Γ →* T) (hπ : Function.Surjective π) (hperf : Group.IsPerfect Γ)
    (σ : Γ →* Equiv.Perm Ω) (htrans : MulAction.IsPretransitive σ.range Ω)
    (hnt : 2 ≤ Fintype.card Ω) (hπker : σ.ker ⊔ π.ker = ⊤)
    (hkerS : Group.IsSolvable π.ker) : False := by
  classical
  letI : Group.IsPerfect Γ := hperf
  have hPne : σ.range ≠ ⊥ := by
    intro hPbot
    haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨χ, ψ, hχψ⟩ := exists_pair_ne Ω
    obtain ⟨p, hp⟩ := htrans.exists_smul_eq χ ψ
    have hp1 : p = 1 := by
      apply Subtype.ext
      exact Subgroup.mem_bot.mp (hPbot ▸ p.2)
    rw [hp1] at hp
    exact hχψ (by simpa using hp)
  have hPmap : ∀ g : Γ, ∃ k ∈ π.ker, σ k = σ g := by
    intro g
    have hg : g ∈ σ.ker ⊔ π.ker := by rw [hπker]; trivial
    rw [Subgroup.mem_sup_of_normal_right (t := π.ker)] at hg
    obtain ⟨a, ha, b, hb, hab⟩ := hg
    refine ⟨b, hb, ?_⟩
    have ha1 : σ a = 1 := MonoidHom.mem_ker.mp ha
    rw [← hab, map_mul, ha1, one_mul]
  have hPsolv : Group.IsSolvable σ.range := by
    let f : π.ker →* σ.range :=
      (σ.comp π.ker.subtype).codRestrict _ fun k => ⟨k, rfl⟩
    have hf : Function.Surjective f := by
      intro p
      obtain ⟨g, hg⟩ := p.2
      obtain ⟨k, hk, hkg⟩ := hPmap g
      refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
      change σ k = ↑p
      rw [hkg, hg]
    haveI : Group.IsSolvable π.ker := hkerS
    exact Group.isSolvable_of_surjective hf
  haveI : Group.IsPerfect σ.range := Group.IsPerfect.range σ
  haveI : Nontrivial σ.range := (Subgroup.nontrivial_iff_ne_bot σ.range).mpr hPne
  exact (Group.IsPerfect.not_isSolvable σ.range) hPsolv

private lemma map_ker_le_center {Γ : Type*} {T : Type} {Ω : Type*} [Group Γ] [Group T]
    [Fintype Ω]
    (π : Γ →* T) (hπ : Function.Surjective π) (hperf : Group.IsPerfect Γ)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (σ : Γ →* Equiv.Perm Ω) (htrans : MulAction.IsPretransitive σ.range Ω)
    (hnt : 2 ≤ Fintype.card Ω) (hkerS : Group.IsSolvable π.ker) :
    Subgroup.map π σ.ker ≤ Subgroup.center T := by
  classical
  letI : Group.IsPerfect Γ := hperf
  haveI : Group.IsPerfect T := Group.IsPerfect.ofSurjective (f := π) hπ
  let σT := CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover hT
  have hσT : Function.Surjective σT :=
    CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover_surjective hT
  have hσTker : σT.ker = Subgroup.center T :=
    CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover_ker hT
  let N : Subgroup T := Subgroup.map π σ.ker
  have hNnormal : N.Normal := (MonoidHom.normal_ker σ).map π hπ
  haveI : N.Normal := hNnormal
  have hmapnorm : (N.map σT).Normal := hNnormal.map σT hσT
  haveI : (N.map σT).Normal := hmapnorm
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map σT) with hbot | htop
  · have hle : N ≤ σT.ker := (Subgroup.map_eq_bot_iff (H := N) (f := σT)).mp hbot
    rwa [hσTker] at hle
  · exfalso
    have hsup : N ⊔ σT.ker = ⊤ := by
      have h := htop
      rw [← MonoidHom.range_eq_top.mpr hσT] at h
      exact codisjoint_iff.mp (Subgroup.map_eq_range_iff.mp h)
    have hNtop : N = ⊤ :=
      CFSG.GroupTheory.eq_top_of_sup_le_center_of_isPerfect (L := N) (Z := σT.ker)
        (by rw [hσTker]) hsup
    have hπker : σ.ker ⊔ π.ker = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hg : π g ∈ N := by
        rw [hNtop]
        trivial
      obtain ⟨h, hh, hgh⟩ := Subgroup.mem_map.mp hg
      have hmem : h⁻¹ * g ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
      have hg' : g = h * (h⁻¹ * g) := by group
      rw [hg']
      exact Subgroup.mul_mem_sup hh hmem
    exact false_of_ker_sup_ker_eq_top π hπ hperf σ htrans hnt hπker hkerS

private lemma exists_surjective_hom_solvable_ker {Γ : Type*} {T : Type} {Ω : Type*}
    [Group Γ] [Group T] [Fintype Ω] [DecidableEq Ω]
    (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker) (hperf : Group.IsPerfect Γ)
    (σ : Γ →* Equiv.Perm Ω)
    (hker : σ.ker ≤
      ((CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker) :
    ∃ φ : σ.range →* alternatingGroup (Fin 6),
      Function.Surjective φ ∧ Group.IsSolvable φ.ker := by
  classical
  letI : Group.IsPerfect Γ := hperf
  let σT := CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover hT
  have hσT : Function.Surjective σT :=
    CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover_surjective hT
  let ψ : Γ →* alternatingGroup (Fin 6) := σT.comp π
  have hψ : Function.Surjective ψ := hσT.comp hπ
  letI : Group.IsSolvable ψ.ker := ker_comp_sigma_isSolvable hT π hkerS
  letI : (σ.ker).Normal := MonoidHom.normal_ker σ
  let fl : Γ ⧸ σ.ker →* alternatingGroup (Fin 6) :=
    QuotientGroup.lift σ.ker ψ hker
  let e : σ.range ≃* Γ ⧸ σ.ker :=
    (QuotientGroup.quotientKerEquivRange σ).symm
  let φ : σ.range →* alternatingGroup (Fin 6) := fl.comp e.toMonoidHom
  have he (g : Γ) : e ⟨σ g, ⟨g, rfl⟩⟩ = QuotientGroup.mk' σ.ker g := by
    show (QuotientGroup.quotientKerEquivRange σ).symm ⟨σ g, _⟩ = _
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext rfl
  have hφeval (g : Γ) : φ ⟨σ g, ⟨g, rfl⟩⟩ = ψ g := by
    show fl (e ⟨σ g, _⟩) = ψ g
    rw [he g]
    exact QuotientGroup.lift_mk' σ.ker hker g
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨g, hg⟩ := hψ y
    exact ⟨⟨σ g, ⟨g, rfl⟩⟩, by rw [hφeval]; exact hg⟩
  let eK : ψ.ker →* φ.ker :=
    { toFun := fun x => ⟨⟨σ (x : Γ), ⟨x, rfl⟩⟩, by
        rw [MonoidHom.mem_ker, hφeval]
        exact x.2⟩
      map_one' := Subtype.ext (Subtype.ext (map_one σ))
      map_mul' := fun x y =>
        Subtype.ext (Subtype.ext (map_mul σ (x : Γ) (y : Γ))) }
  have heK : Function.Surjective eK := by
    intro y
    obtain ⟨x, hx⟩ := y.1.2
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change ψ x = 1
      have hy : φ y.1 = 1 := y.2
      rw [show y.1 = ⟨σ x, ⟨x, rfl⟩⟩ from Subtype.ext hx.symm] at hy
      rwa [hφeval] at hy
    · apply Subtype.ext
      exact Subtype.ext hx
  have hφker : Group.IsSolvable φ.ker := Group.isSolvable_of_surjective heK
  exact ⟨φ, hφ, hφker⟩

private lemma card_actionSet_eq_six {Γ : Type*} {T : Type} {Ω : Type*} [Group Γ]
    [Group T] [Fintype Ω] [DecidableEq Ω]
    (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hkerS : Group.IsSolvable π.ker) (hperf : Group.IsPerfect Γ)
    (σ : Γ →* Equiv.Perm Ω) (htrans : MulAction.IsPretransitive σ.range Ω)
    (hcard9 : Fintype.card Ω ≤ 9)
    (hker : σ.ker ≤
      ((CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker) :
    Fintype.card Ω = 6 ∧ σ.range = alternatingGroup Ω := by
  classical
  letI : Group.IsPerfect Γ := hperf
  obtain ⟨φ, hφ, hφker⟩ :=
    exists_surjective_hom_solvable_ker π hπ hT hkerS hperf σ hker
  exact card_eq_six_and_eq_alternatingGroup hcard9 σ.range htrans
    (Group.IsPerfect.range σ) φ hφ hφker

private lemma finrank_le_of_smul_eq {K V Γ Ω : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Group Γ] {ρ : Representation K Γ V}
    (W : Ω → Submodule K V)
    (σ : Γ →* Equiv.Perm Ω) (hmap : ∀ g χ, (W χ).map (ρ g) = W (σ g χ))
    {χ ψ : Ω} {g : Γ} (hg : σ g χ = ψ) :
    Module.finrank K (W χ) ≤ Module.finrank K (W ψ) := by
  let f : (W χ) →ₗ[K] (W ψ) :=
    ((ρ g).comp (W χ).subtype).codRestrict (W ψ) fun v => by
      have hv : ρ g (v : V) ∈ (W χ).map (ρ g) := ⟨v, v.2, rfl⟩
      rwa [hmap g χ, hg] at hv
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  intro x y hxy
  apply Subtype.ext
  have h1 : ρ g (x : V) = ρ g (y : V) := congrArg Subtype.val hxy
  have h2 := congrArg (ρ g⁻¹) h1
  simpa [← Module.End.mul_apply, ← map_mul] using h2

private lemma finrank_weightSpace_eq_of_transitive {K V Γ Ω : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group Γ]
    {ρ : Representation K Γ V}
    (W : Ω → Submodule K V) (σ : Γ →* Equiv.Perm Ω)
    (hmap : ∀ g χ, (W χ).map (ρ g) = W (σ g χ))
    (htrans : ∀ χ ψ : Ω, ∃ g : Γ, σ g χ = ψ) (χ ψ : Ω) :
    Module.finrank K (W χ) = Module.finrank K (W ψ) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨g, hg⟩ := htrans χ ψ
    exact finrank_le_of_smul_eq W σ hmap hg
  · obtain ⟨g, hg⟩ := htrans ψ χ
    exact finrank_le_of_smul_eq W σ hmap hg

private lemma finrank_eq_sum_finrank_of_iSupIndep {K V Ω : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype Ω] [DecidableEq Ω]
    (W : Ω → Submodule K V) (hind : iSupIndep W) (htop : ⨆ i, W i = ⊤) :
    Module.finrank K V = ∑ i, Module.finrank K (W i) := by
  let hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let := hint.chooseDecomposition
  rw [(DirectSum.decomposeLinearEquiv W).finrank_eq, Module.finrank_directSum]

private lemma weightHom_transitive {K V Γ : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group Γ] [Finite Γ]
    {ρ : Representation K Γ V} (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    {Q : Subgroup Γ} [Q.Normal] (hQc : IsMulCommutative Q)
    (hQchar : ((Nat.card Q : ℕ) : K) ≠ 0) (hQZ : ¬ Q ≤ Subgroup.center Γ)
    [Fintype (CFSG.Walter.JT.weights ρ Q)] :
    MulAction.IsPretransitive (weightHom ρ Q).range (CFSG.Walter.JT.weights ρ Q) ∧
      2 ≤ Fintype.card (CFSG.Walter.JT.weights ρ Q) ∧
      Fintype.card (CFSG.Walter.JT.weights ρ Q) ≤ Module.finrank K V := by
  classical
  have hN : ∀ a ∈ Q, ∀ b ∈ Q, ρ a * ρ b = ρ b * ρ a := by
    intro a ha b hb
    have hcomm : a * b = b * a :=
      congrArg Subtype.val (hQc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, hcomm]
  let Ω := CFSG.Walter.JT.weights ρ Q
  have hdecomp := CFSG.Walter.JT.iSupIndep_weightSpace_and_iSup_eq_top ρ Q hN hQchar
  have hind_all : iSupIndep (CFSG.Walter.JT.weightSpace ρ Q) := hdecomp.1
  have hind : iSupIndep (fun χ : Ω => CFSG.Walter.JT.weightSpace ρ Q χ) :=
    hind_all.comp Subtype.coe_injective
  have htop_all : ⨆ χ : Q → K, CFSG.Walter.JT.weightSpace ρ Q χ = ⊤ := hdecomp.2
  have htop : ⨆ χ : Ω, CFSG.Walter.JT.weightSpace ρ Q χ = ⊤ := by
    rw [iSup_weightSpace_eq_iSup_weights, htop_all]
  have hfin := CFSG.Walter.JT.finite_weights_and_card_le ρ Q hN hQchar
  have hcard : Fintype.card (CFSG.Walter.JT.weights ρ Q) ≤ Module.finrank K V := by
    rw [← Nat.card_eq_fintype_card]
    exact hfin.2
  haveI : Nontrivial V := nontrivial_of_isIrreducible hirr
  have hΩne : Nonempty Ω := by
    by_contra h
    haveI : IsEmpty Ω := not_nonempty_iff.mp h
    have hempty : (⨆ χ : Ω, CFSG.Walter.JT.weightSpace ρ Q χ) = ⊥ :=
      iSup_of_empty _
    rw [hempty] at htop
    exact bot_ne_top htop
  obtain ⟨χ₀⟩ := hΩne
  have hmap : ∀ (g : Γ) (χ : Ω),
      (CFSG.Walter.JT.weightSpace ρ Q χ).map (ρ g) =
        CFSG.Walter.JT.weightSpace ρ Q (weightHom ρ Q g χ) :=
    fun g χ => weightSpace_map_weightHom ρ Q g χ
  have htrans_one (χ : Ω) : ∀ ψ : Ω, ∃ g : Γ, weightHom ρ Q g χ = ψ :=
    transitive_of_weightAction (Ω := Ω) hirr
      (fun χ : Ω => CFSG.Walter.JT.weightSpace ρ Q χ) (weightHom ρ Q)
      hmap hind htop (fun χ : Ω => χ.2) χ
  have htrans : MulAction.IsPretransitive (weightHom ρ Q).range Ω :=
    MulAction.IsPretransitive.mk fun χ ψ => by
      obtain ⟨g, hg⟩ := htrans_one χ ψ
      exact ⟨⟨weightHom ρ Q g, ⟨g, rfl⟩⟩, hg⟩
  have hnt : 2 ≤ Fintype.card Ω := by
    rw [← Nat.card_eq_fintype_card]
    exact two_le_card_weights hfaith htop hQZ
  exact ⟨htrans, hnt, hcard⟩

private lemma weightHom_ker_le_sigma {K V Γ : Type*} {T : Type} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Group Γ] [Finite Γ] [Group T]
    {ρ : Representation K Γ V} (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    {Q : Subgroup Γ} [Q.Normal] (hQc : IsMulCommutative Q)
    (hQchar : ((Nat.card Q : ℕ) : K) ≠ 0) (hQZ : ¬ Q ≤ Subgroup.center Γ)
    (hperf : Group.IsPerfect Γ)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (π : Γ →* T) (hπ : Function.Surjective π) (hkerS : Group.IsSolvable π.ker)
    [Fintype (CFSG.Walter.JT.weights ρ Q)] :
    (weightHom ρ Q).ker ≤
      ((CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker := by
  obtain ⟨htrans, hnt, -⟩ := weightHom_transitive hirr hfaith hQc hQchar hQZ
  let σT := CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover hT
  have hσTker : σT.ker = Subgroup.center T :=
    CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover_ker hT
  intro g hg
  change π g ∈ σT.ker
  rw [hσTker]
  exact map_ker_le_center π hπ hperf hT (weightHom ρ Q) htrans hnt hkerS
    ⟨g, hg, rfl⟩

private lemma finrank_weightSpace_eq_one {K V Ω : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Fintype Ω] [DecidableEq Ω]
    (W : Ω → Submodule K V) (hind : iSupIndep W) (htop : ⨆ i, W i = ⊤)
    (hcard6 : Fintype.card Ω = 6) (hdim : Module.finrank K V ≤ 9)
    (hdimEq : ∀ χ ψ, Module.finrank K (W χ) = Module.finrank K (W ψ))
    (χ₀ : Ω) (hWne : W χ₀ ≠ ⊥) :
    ∀ χ, Module.finrank K (W χ) = 1 := by
  have hWsum := finrank_eq_sum_finrank_of_iSupIndep W hind htop
  let d := Module.finrank K (W χ₀)
  have hdvd : ∀ χ, Module.finrank K (W χ) = d := fun χ => hdimEq χ χ₀
  have hsumd : Module.finrank K V = Fintype.card Ω * d := by
    rw [hWsum]
    calc
      ∑ χ : Ω, Module.finrank K (W χ) = ∑ _χ : Ω, d :=
        Finset.sum_congr rfl fun χ _ => hdvd χ
      _ = Fintype.card Ω * d := by
        rw [Finset.sum_const, Finset.card_univ]
        simp
  have hdpos : 0 < d := by
    rw [show d = Module.finrank K (W χ₀) from rfl]
    exact (Submodule.one_le_finrank_iff).mpr hWne
  have h6d : 6 * d ≤ 9 := by
    have := hdim
    rwa [hsumd, hcard6] at this
  have hd1 : d = 1 := by omega
  intro χ
  rw [hdvd χ, hd1]

private lemma exists_six_lines_of_alt {𝕜 V Γ Ω : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [Group Γ] [Fintype Ω] [DecidableEq Ω]
    (ρ : Representation 𝕜 Γ V) (W : Ω → Submodule 𝕜 V) (σ : Γ →* Equiv.Perm Ω)
    (hline : ∀ χ, Module.finrank 𝕜 (W χ) = 1) (hind : iSupIndep W)
    (htop : ⨆ i, W i = ⊤) (hmap : ∀ g χ, (W χ).map (ρ g) = W (σ g χ))
    (hcard6 : Fintype.card Ω = 6) (hrange : σ.range = alternatingGroup Ω) :
    ∃ (W' : Fin 6 → Submodule 𝕜 V) (σ' : Γ →* Equiv.Perm (Fin 6)),
      (∀ i, Module.finrank 𝕜 (W' i) = 1) ∧ iSupIndep W' ∧ ⨆ i, W' i = ⊤ ∧
      (∀ g i, (W' i).map (ρ g) = W' (σ' g i)) ∧
      σ'.range = alternatingGroup (Fin 6) := by
  classical
  let e : Ω ≃ Fin 6 := Fintype.equivFinOfCardEq hcard6
  let W' : Fin 6 → Submodule 𝕜 V := fun i => W (e.symm i)
  let σ' : Γ →* Equiv.Perm (Fin 6) :=
    (e.permCongrHom : Equiv.Perm Ω →* Equiv.Perm (Fin 6)).comp σ
  have hWline : ∀ i, Module.finrank 𝕜 (W' i) = 1 := fun i => hline (e.symm i)
  have hWind : iSupIndep W' := hind.comp e.symm.injective
  have hWtop : ⨆ i, W' i = ⊤ := by
    rw [Equiv.iSup_comp (e := e.symm) (g := W), htop]
  have hWmap : ∀ g i, (W' i).map (ρ g) = W' (σ' g i) := by
    intro g i
    rw [show W' i = W (e.symm i) from rfl, hmap g (e.symm i)]
    congr 1
    simp [σ', Equiv.permCongr_apply]
  have hWrange : σ'.range = alternatingGroup (Fin 6) := by
    have hmap_alt : (alternatingGroup Ω).map
        (e.permCongrHom : Equiv.Perm Ω →* Equiv.Perm (Fin 6)) =
        alternatingGroup (Fin 6) := by
      simp [Subgroup.ext_iff, Subgroup.map_equiv_eq_comap_symm]
    rw [show σ'.range = (σ.range).map
      (e.permCongrHom : Equiv.Perm Ω →* Equiv.Perm (Fin 6)) from by
      rw [MonoidHom.range_comp]]
    rw [hrange, hmap_alt]
  exact ⟨W', σ', hWline, hWind, hWtop, hWmap, hWrange⟩

theorem exists_six_lines {𝕜 : Type*} [Field 𝕜] [IsAlgClosed 𝕜] {p : ℕ} [CharP 𝕜 p]
    (hp : p.Prime)
    {Γ : Type*} [Group Γ] [Finite Γ] (hperf : Group.IsPerfect Γ)
    {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    (ρ : Representation 𝕜 Γ V) (hirr : ρ.IsIrreducible) (hfaith : Function.Injective ρ)
    (hdim : Module.finrank 𝕜 V ≤ 9)
    {T : Type} [Group T] (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) (hkerS : Group.IsSolvable π.ker)
    {r : ℕ} (hr : r.Prime) {Q : Subgroup Γ} (hQn : Q.Normal)
    (hQr : IsPGroup r Q) (hQc : IsMulCommutative Q) (hQZ : ¬ Q ≤ Subgroup.center Γ) :
    ∃ (W : Fin 6 → Submodule 𝕜 V) (σ : Γ →* Equiv.Perm (Fin 6)),
      (∀ i, Module.finrank 𝕜 (W i) = 1) ∧ iSupIndep W ∧ ⨆ i, W i = ⊤ ∧
      (∀ g i, (W i).map (ρ g) = W (σ g i)) ∧ σ.range = alternatingGroup (Fin 6) := by
  classical
  letI : Q.Normal := hQn
  have hrp : r ≠ p := fun h => r_ne_p hp hirr hfaith hQn hQr hQZ h
  have hQchar : ((Nat.card Q : ℕ) : 𝕜) ≠ 0 :=
    card_Q_cast_ne_zero hp hr hQr hQZ hrp
  have hN : ∀ a ∈ Q, ∀ b ∈ Q, ρ a * ρ b = ρ b * ρ a := by
    intro a ha b hb
    have hcomm : a * b = b * a :=
      congrArg Subtype.val (hQc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [← map_mul, ← map_mul, hcomm]
  let Ω := CFSG.Walter.JT.weights ρ Q
  have hfin := CFSG.Walter.JT.finite_weights_and_card_le ρ Q hN hQchar
  haveI : Finite Ω := hfin.1
  letI : Fintype (CFSG.Walter.JT.weights ρ Q) := Fintype.ofFinite Ω
  have hdecomp := CFSG.Walter.JT.iSupIndep_weightSpace_and_iSup_eq_top ρ Q hN hQchar
  have hind_all : iSupIndep (CFSG.Walter.JT.weightSpace ρ Q) := hdecomp.1
  have hind : iSupIndep (fun χ : Ω => CFSG.Walter.JT.weightSpace ρ Q χ) :=
    hind_all.comp Subtype.coe_injective
  have htop_all : ⨆ χ : Q → 𝕜, CFSG.Walter.JT.weightSpace ρ Q χ = ⊤ := hdecomp.2
  have htop : ⨆ χ : Ω, CFSG.Walter.JT.weightSpace ρ Q χ = ⊤ := by
    rw [iSup_weightSpace_eq_iSup_weights, htop_all]
  obtain ⟨htrans, hnt, hcard_le⟩ :=
    weightHom_transitive hirr hfaith hQc hQchar hQZ
  have hcard9 : Fintype.card Ω ≤ 9 := hcard_le.trans hdim
  have hσker_le : (weightHom ρ Q).ker ≤
      ((CFSG.RankThree.PartTwo.Sec16.ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker :=
    weightHom_ker_le_sigma hirr hfaith hQc hQchar hQZ hperf hT π hπ hkerS
  obtain ⟨hcard6, hPalt⟩ :=
    card_actionSet_eq_six π hπ hT hkerS hperf (weightHom ρ Q) htrans hcard9 hσker_le
  haveI : Nonempty Ω := Fintype.card_pos_iff.mp (by rw [hcard6]; norm_num)
  obtain ⟨χ₀⟩ := ‹Nonempty Ω›
  have hdimEq : ∀ χ ψ : Ω,
      Module.finrank 𝕜 (CFSG.Walter.JT.weightSpace ρ Q χ) =
        Module.finrank 𝕜 (CFSG.Walter.JT.weightSpace ρ Q ψ) :=
    finrank_weightSpace_eq_of_transitive
      (fun χ : Ω => CFSG.Walter.JT.weightSpace ρ Q χ) (weightHom ρ Q)
      (fun g χ => weightSpace_map_weightHom ρ Q g χ)
      (fun χ ψ => exists_smul_eq_of_isPretransitive (weightHom ρ Q) htrans χ ψ)
  have hAllOne : ∀ χ : Ω,
      Module.finrank 𝕜 (CFSG.Walter.JT.weightSpace ρ Q χ) = 1 :=
    finrank_weightSpace_eq_one
      (fun χ : Ω => CFSG.Walter.JT.weightSpace ρ Q χ) hind htop hcard6 hdim hdimEq
      χ₀ χ₀.2
  exact exists_six_lines_of_alt ρ
    (fun χ : Ω => CFSG.Walter.JT.weightSpace ρ Q χ) (weightHom ρ Q) hAllOne hind htop
    (fun g χ => weightSpace_map_weightHom ρ Q g χ) hcard6 hPalt

end CFSG.RankThree.PartTwo.Sec16.Kcd166
