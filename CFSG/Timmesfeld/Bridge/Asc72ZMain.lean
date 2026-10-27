module

public import CFSG.Timmesfeld.Bridge.Asc72ZCore
public import CFSG.Timmesfeld.Bridge.Asc72YFinal

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.BenderSuzuki CFSG.Timmesfeld.Bridge.Asc72.AltFive

variable {G : Type} [Group G] {D : Set G}

theorem exists_rho [Finite G] (hD : IsOddTransp D)
    (hN : IsNormalSet D) {z : G} (hzz : z * z = 1) (hzH : z ∈ localGroup D z) (hzD : z ∉ D)
    (hz2 : ∀ r ∈ D, ∀ s ∈ D, r ≠ s → Commute r s → z ≠ r * s)
    (hO2 : ∀ q ∈ CFSG.pCore 2 (localGroup D z), (q : G) = 1 ∨ (q : G) = z)
    (hL : Nonempty (localGroup D z ⧸ zStar (localGroup D z) ≃* PSL2Model 2))
    {c : localGroup D z} (hc : c ∈ localSet D z) {a : G} (haa : a * a = 1)
    (haz : Commute a z) :
    ∃ (ρ : localGroup D z →* alternatingGroup (Fin 5)) (φ : MulAut (localGroup D z))
      (ψ : MulAut (alternatingGroup (Fin 5))), Function.Surjective ρ ∧ ρ c = c0 ∧
      (∀ x y : localGroup D z, x ∈ localSet D z → y ∈ localSet D z → ρ x = ρ y → x = y) ∧
      (∀ x y : localGroup D z, x ∈ localSet D z → y ∈ localSet D z →
        Commute (ρ x) (ρ y) → Commute x y) ∧
      (∀ x : localGroup D z, x ∈ localSet D z → ρ x ≠ 1) ∧
      (∀ p : localGroup D z, ρ p = 1 →
        ∃ m : ℕ, Odd m ∧ ((p : G) ^ m = 1 ∨ (p : G) ^ m = z)) ∧
      (∀ x, (φ x : G) = a * x * a⁻¹) ∧ (∀ x, ρ (φ x) = ψ (ρ x)) ∧ (∀ y, ψ (ψ y) = y) := by
  classical
  set z' : localGroup D z := ⟨z, hzH⟩ with hz'def
  have hz'c : z' ∈ Subgroup.center (localGroup D z) :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_localGroup g.2).eq
  have : (Subgroup.zpowers z').Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz'c)
  have hzz' : z' * z' = 1 := Subtype.ext hzz
  have hO2' : CFSG.pCore 2 (localGroup D z) ≤ Subgroup.zpowers z' := by
    intro q hq
    rcases hO2 q hq with h | h
    · rw [show q = 1 from Subtype.ext h]
      exact Subgroup.one_mem _
    · rw [show q = z' from Subtype.ext h]
      exact Subgroup.mem_zpowers _
  have hE : IsOddTransp (localSet D z) := (hD.mono fun x hx => hx.1).preimage _
  have hzE : z' ∉ localSet D z := fun h => hzD h.1
  have hz2' : ∀ r ∈ localSet D z, ∀ s ∈ localSet D z, r ≠ s → Commute r s → z' ≠ r * s :=
    fun r hr s hs hrs hc heq => hz2 r hr.1 s hs.1 (fun h => hrs (Subtype.ext h))
      (commute_coe_iff.mpr hc) (congrArg Subtype.val heq)
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hmapH : (localGroup D z).map (MulAut.conj a).toMonoidHom = localGroup D z := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact conj_mem_localGroup hN haz hx
    · intro x hx
      refine ⟨a * x * a⁻¹, conj_mem_localGroup hN haz hx, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hainv]
      rw [show a * (a * x * a) * a = (a * a) * x * (a * a) by group, haa, one_mul, mul_one]
  let φ : MulAut (localGroup D z) :=
    ((MulAut.conj a).subgroupMap (localGroup D z)).trans (MulEquiv.subgroupCongr
      ((show (localGroup D z).map (MulAut.conj a : G →* G) =
        (localGroup D z).map (MulAut.conj a).toMonoidHom from rfl).trans hmapH))
  have hφ : ∀ x : localGroup D z, ((φ x : localGroup D z) : G) = a * x * a⁻¹ := fun x => rfl
  have hφφ : ∀ x : localGroup D z, φ (φ x) = x := fun x => Subtype.ext (by
    rw [hφ, hφ, hainv, show a * (a * (x : G) * a) * a = (a * a) * x * (a * a) by group, haa,
      one_mul, mul_one])
  set π := QuotientGroup.mk' (zStar (localGroup D z)) with hπdef
  let α : MulAut (localGroup D z ⧸ zStar (localGroup D z)) :=
    QuotientGroup.congr (zStar (localGroup D z)) (zStar (localGroup D z)) φ (map_zStar_eq φ)
  have hα : ∀ x : localGroup D z, α (π x) = π (φ x) := fun x =>
    QuotientGroup.congr_mk (zStar (localGroup D z)) (zStar (localGroup D z)) φ
      (map_zStar_eq φ) x
  have hαα : ∀ q, α (α q) = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (zStar (localGroup D z)) q
    rw [hα, hα, hφφ]
  obtain ⟨e⟩ := hL
  obtain ⟨e5⟩ := nonempty_psl2Model_two_equiv
  set E₀ : localGroup D z ⧸ zStar (localGroup D z) ≃* alternatingGroup (Fin 5) := e.trans e5
    with hE₀
  have hcc : c * c = 1 := Subtype.ext (hD.mul_self_eq_one hc.1)
  have hc1 : E₀ (π c) ≠ 1 := fun h => CentralQuot.mk_zStar_ne_one hzz' hE hzE hO2' hc
    (E₀.injective (h.trans (map_one E₀).symm))
  have hcc' : E₀ (π c) * E₀ (π c) = 1 := by rw [← map_mul, ← map_mul, hcc, map_one, map_one]
  obtain ⟨σ, hσ⟩ := exists_conj_c0 _ hcc' hc1
  set E' : localGroup D z ⧸ zStar (localGroup D z) ≃* alternatingGroup (Fin 5) :=
    E₀.trans (MulAut.conj σ) with hE'
  have hE'q : ∀ q, E' q = σ * E₀ q * σ⁻¹ := fun q => rfl
  set ρ : localGroup D z →* alternatingGroup (Fin 5) := E'.toMonoidHom.comp π with hρdef
  have hρx : ∀ x, ρ x = E' (π x) := fun x => rfl
  let ψ : MulAut (alternatingGroup (Fin 5)) := (E'.symm.trans α).trans E'
  have hψ : ∀ y, ψ y = E' (α (E'.symm y)) := fun y => rfl
  have hπ1 : ∀ x : localGroup D z, ρ x = 1 → π x = 1 := fun x h =>
    E'.injective (((hρx x).symm.trans h).trans (map_one E').symm)
  refine ⟨ρ, φ, ψ, fun y => ?_, ?_, fun x y hx hy h => ?_, fun x y hx hy h => ?_,
    fun x hx h => ?_, fun p hp => ?_, hφ, fun x => ?_, fun y => ?_⟩
  · obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (zStar (localGroup D z)) (E'.symm y)
    refine ⟨x, ?_⟩
    rw [hρx]
    show E' (QuotientGroup.mk' (zStar (localGroup D z)) x) = y
    rw [hx, MulEquiv.apply_symm_apply]
  · rw [hρx, hE'q]
    exact hσ
  · exact CentralQuot.eq_of_mk_zStar_eq hzz' hE hO2' hz2' hx hy (E'.injective h)
  · refine CentralQuot.commute_of_mk_zStar hzz' hE hO2' hz2' hx hy ?_
    have h1 : Commute (E'.symm (ρ x)) (E'.symm (ρ y)) := h.map E'.symm
    rwa [hρx, hρx, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h1
  · exact CentralQuot.mk_zStar_ne_one hzz' hE hzE hO2' hx (hπ1 x h)
  · have hpS : p ∈ zStar (localGroup D z) := (QuotientGroup.eq_one_iff p).mp (hπ1 p hp)
    obtain ⟨m, hm, hpm⟩ := CentralQuot.exists_odd_pow_mem hzz' hO2' hpS
    refine ⟨m, hm, ?_⟩
    rcases (mem_zpowers_of_mul_self hzz').mp hpm with h | h
    · left
      simpa using congrArg Subtype.val h
    · right
      simpa [hz'def] using congrArg Subtype.val h
  · rw [hρx, hρx, hψ, MulEquiv.symm_apply_apply, hα]
  · rw [hψ, hψ, MulEquiv.symm_apply_apply, hαα, MulEquiv.apply_symm_apply]


theorem false_of_psl2 [Finite G] (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hZ : Subgroup.center G = ⊥) (hnsq : ¬ MeetsSq D) {u w v : G} (htri : IsTriangle D u w v)
    {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) (huw : ¬ Reach D u w)
    (hO2 : ∀ q ∈ CFSG.pCore 2 (localGroup D ((u * v * w) ^ n)),
      (q : G) = 1 ∨ (q : G) = (u * v * w) ^ n)
    (hL : Nonempty (localGroup D ((u * v * w) ^ n) ⧸ zStar (localGroup D ((u * v * w) ^ n)) ≃*
      PSL2Model 2)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := hS.oddT
  have hN := hS.normal
  obtain ⟨hzz, hz1, hzu, hzv, hzw, -⟩ := htri.third_kind hD hN hn hord
  obtain ⟨hu', hv', hw', huvz⟩ := thirdKind_mem_centSet hS htri hn hord
  have hzH := thirdKind_z_mem_localGroup hS htri hn hord
  have hSH := localSetup hS htri hn hord huw
  have hzD := thirdKind_z_not_mem hS htri hn hord huw
  have hz2 : ∀ r ∈ D, ∀ s ∈ D, r ≠ s → Commute r s → (u * v * w) ^ n ≠ r * s :=
    fun r hr s hs hrs hc heq =>
      false_of_eq_mul_of_not_reach hS htri.1 htri.2.2.1 hzu.symm hzw.symm huw hr hs hrs hc heq
  have huv := htri.2.2.2.2.1
  have hdab := (hD.commute_mul_iff htri.1 htri.2.1 huvz.1 htri.2.2.2.1 huv).mp
    ((Commute.refl (u * v)).mul_left (hzu.mul_right hzv))
  have hpair : ({u, v, u * v * (u * v * w) ^ n} : Set G).Pairwise Commute := by
    have h1 := huv
    have h2 := hdab.1.symm
    have h3 := hdab.2.symm
    have h1' := h1.symm
    have h2' := h2.symm
    have h3' := h3.symm
    intro s hs t ht _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl <;>
      first | exact Commute.refl _ | assumption
  have hA : IsPGroup 2 (Subgroup.closure ({u, v, u * v * (u * v * w) ^ n} : Set G)) := by
    refine isPGroup_closure_of_pairwise hpair ?_
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hD.mul_self_eq_one htri.1
    · exact hD.mul_self_eq_one htri.2.1
    · exact hD.mul_self_eq_one huvz.1
  obtain ⟨S₀, hS₀⟩ := hA.exists_le_sylow
  have huS : u ∈ S₀ := hS₀ (Subgroup.subset_closure (by simp))
  have hvS : v ∈ S₀ := hS₀ (Subgroup.subset_closure (by simp))
  have hdS : u * v * (u * v * w) ^ n ∈ S₀ := hS₀ (Subgroup.subset_closure (by simp))
  obtain ⟨h3, hzc, a, haS, -, haconj, haa, haL, hfix⟩ :=
    sylow_data hS hrad hZ hnsq htri hn hord huw hO2 S₀ huS hvS hdS
  have haz : Commute a ((u * v * w) ^ n) := hzc a haS
  set z := (u * v * w) ^ n with hzdef
  have huu := hD.mul_self_eq_one htri.1
  have hvv := hD.mul_self_eq_one htri.2.1
  have hdu : u * v * z ≠ u := by
    intro h
    apply hzD
    have h1 : v * z = 1 := by
      calc v * z = u⁻¹ * (u * v * z) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
    rw [show z = v⁻¹ from eq_inv_of_mul_eq_one_right h1, hD.inv_eq htri.2.1]
    exact htri.2.1
  have hdv : u * v * z ≠ v := by
    intro h
    apply hzD
    have h1 : u * z = 1 := by
      have e : u * v * z = u * z * v := by rw [mul_assoc u v z, ← hzv.eq, ← mul_assoc]
      rw [e] at h
      calc u * z = u * z * v * v⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]
    rw [show z = u⁻¹ from eq_inv_of_mul_eq_one_right h1, hD.inv_eq htri.1]
    exact htri.1
  have hsub : ({u, v, u * v * z} : Set G) ⊆ D ∩ (S₀ : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [⟨htri.1, huS⟩, ⟨htri.2.1, hvS⟩, ⟨huvz.1, hdS⟩]
  have heq : ({u, v, u * v * z} : Set G) = D ∩ (S₀ : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [h3, Set.ncard_eq_three.mpr ⟨u, v, u * v * z, htri.2.2.2.1, hdu.symm, hdv.symm, rfl⟩]
  have hmem3 : ∀ x ∈ D ∩ (S₀ : Set G), x = u ∨ x = v ∨ x = u * v * z := by
    intro x hx
    rw [← heq] at hx
    simpa using hx
  have hsub3 : ∀ x, (x = u ∨ x = v ∨ x = u * v * z) → x ∈ D ∩ (S₀ : Set G) := fun x hx =>
    hsub (by simpa using hx)
  have hzu' : z * u = v * (u * v * z) := by
    calc z * u = u * z := hzu.eq
      _ = u * (v * v) * z := by rw [hvv, mul_one]
      _ = u * v * v * z := by simp only [mul_assoc]
      _ = v * u * v * z := by rw [huv.eq]
      _ = v * (u * v * z) := by simp only [mul_assoc]
  have hzv' : z * v = u * (u * v * z) := by
    calc z * v = v * z := hzv.eq
      _ = (u * u) * v * z := by rw [huu, one_mul]
      _ = u * (u * v * z) := by simp only [mul_assoc]
  have hzd' : z * (u * v * z) = u * v := by
    calc z * (u * v * z) = z * u * v * z := by simp only [mul_assoc]
      _ = u * z * v * z := by rw [hzu.eq]
      _ = u * (z * v) * z := by simp only [mul_assoc]
      _ = u * (v * z) * z := by rw [hzv.eq]
      _ = u * v * (z * z) := by simp only [mul_assoc]
      _ = u * v := by rw [hzz, mul_one]
  obtain ⟨c, e₁, e₂, hcm, he₁m, he₂m, hce₁, hce₂, he₁₂, hcc₁, hcc₂, hc₁₂, hac, hae, hzce⟩ :=
    exists_fix_swap haa htri.2.2.2.1 hdu.symm hdv.symm huv hdab.1.symm hdab.2.symm hzu' hzv'
      hzd' (fun x hx => hmem3 _ (haL x (hsub3 x hx)))
      (fun x y hx hy hxy hax hay => hfix ⟨x, hsub3 x hx, y, hsub3 y hy, hxy, hax, hay⟩)
  have hΓ : ∀ x, (x = u ∨ x = v ∨ x = u * v * z) → x ∈ centSet D z := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    exacts [hu', hv', huvz]
  have hcΓ := hΓ c hcm
  have he₁Γ := hΓ e₁ he₁m
  have he₂Γ := hΓ e₂ he₂m
  have huc : Reach D u c := by
    rcases hcm with h | h | h <;> rw [h]
    · exact reach_refl _
    · exact reach_of_commute htri.1 htri.2.1 huv
    · exact reach_of_commute htri.1 huvz.1 hdab.1.symm
  have hsq1 : InSq D (z * c) := ⟨e₁, he₁Γ.1, e₂, he₂Γ.1, he₁₂, hc₁₂, hzce⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp haconj
  have hc'Γ : g⁻¹ * c * g ∈ centSet D z := by
    refine ⟨by simpa using hN g⁻¹ c hcΓ.1, ?_⟩
    have h1 : Commute (g⁻¹ * c * g) (g⁻¹ * a * g) := by
      simpa using (Commute.conj_iff g⁻¹).mpr hac.symm
    rwa [show g⁻¹ * a * g = z by rw [← hg]; group] at h1
  obtain ⟨k, hk⟩ := isConj_iff.mp (hSH.isConj
    (show (⟨c, mem_localGroup_of_mem hcΓ⟩ : localGroup D z) ∈ localSet D z from hcΓ)
    (show (⟨g⁻¹ * c * g, mem_localGroup_of_mem hc'Γ⟩ : localGroup D z) ∈ localSet D z from
      hc'Γ))
  have hk' : (k : G) * c * (k : G)⁻¹ = g⁻¹ * c * g := by
    simpa using congrArg Subtype.val hk
  have hkz : Commute (k : G) z := commute_of_mem_localGroup k.2
  have hsq2 : InSq D (z * (g⁻¹ * c * g)) := by
    have e : (k : G) * (z * c) * (k : G)⁻¹ = z * ((k : G) * c * (k : G)⁻¹) := by
      calc (k : G) * (z * c) * (k : G)⁻¹ = ((k : G) * z) * c * (k : G)⁻¹ := by group
        _ = (z * k) * c * (k : G)⁻¹ := by rw [hkz.eq]
        _ = z * ((k : G) * c * (k : G)⁻¹) := by group
    have h1 := hsq1.conj hN k
    rwa [e, hk'] at h1
  have hsq3 : InSq D (a * c) := by
    have h1 := hsq2.conj hN g
    rwa [show g * (z * (g⁻¹ * c * g)) * g⁻¹ = g * z * g⁻¹ * c by group, hg] at h1
  set c' : localGroup D z := ⟨c, mem_localGroup_of_mem hcΓ⟩ with hc'def
  have hcL : c' ∈ localSet D z := hcΓ
  obtain ⟨ρ, φ, ψ, hρ, hρc, hinj, hcomm, hne, hker, hφ, hρφ, hψψ⟩ :=
    exists_rho hD hN hzz hzH hzD hz2 hO2 hL hcL haa haz
  set e₁' : localGroup D z := ⟨e₁, mem_localGroup_of_mem he₁Γ⟩ with he₁'def
  set e₂' : localGroup D z := ⟨e₂, mem_localGroup_of_mem he₂Γ⟩ with he₂'def
  have he₁L : e₁' ∈ localSet D z := he₁Γ
  have he₂L : e₂' ∈ localSet D z := he₂Γ
  have hφc : φ c' = c' := Subtype.ext (by
    rw [hφ]
    show a * c * a⁻¹ = c
    rw [hac.eq, mul_inv_cancel_right])
  have hφe : φ e₁' = e₂' := Subtype.ext (by rw [hφ]; exact hae)
  have hψc : ψ c0 = c0 := by rw [← hρc, ← hρφ, hφc]
  have hsq : ∀ x : localGroup D z, x ∈ localSet D z → ρ x * ρ x = 1 := fun x hx => by
    rw [← map_mul, show x * x = 1 from Subtype.ext (hD.mul_self_eq_one hx.1), map_one]
  have hcomm' : ∀ x y : localGroup D z, Commute (x : G) (y : G) → ρ x * ρ y = ρ y * ρ x :=
    fun x y h => ((commute_coe_iff.mp h).map ρ).eq
  have hne' : ∀ x y : localGroup D z, x ∈ localSet D z → y ∈ localSet D z → (x : G) ≠ y →
      ρ x ≠ ρ y := fun x y hx hy hxy h => hxy (congrArg Subtype.val (hinj x y hx hy h))
  obtain ⟨hx0, γA, kA, hγA, hψγ, hkA⟩ := aut_facts ψ hψψ hψc (hsq _ he₁L) (hsq _ he₂L)
    (by rw [← hρc]; exact hcomm' _ _ hcc₁.symm) (by rw [← hρc]; exact hcomm' _ _ hcc₂.symm)
    (hne _ he₁L) (hne _ he₂L) (by rw [← hρc]; exact hne' _ _ he₁L hcL hce₁.symm)
    (by rw [← hρc]; exact hne' _ _ he₂L hcL hce₂.symm) (hne' _ _ he₁L he₂L he₁₂)
    (by rw [← hρφ, hφe])
  obtain ⟨γ, hγL, haγ, -, hργ⟩ :=
    exists_gamma hN ρ hρ hinj hcL hρc haz φ hφ ψ hρφ hγA hψγ hkA
  obtain ⟨g', hg'⟩ := exists_conj_mul ρ hρ haa φ hφ ψ hρφ hx0 hker hρc hac
    (hD.mul_self_eq_one hcΓ.1)
  rcases hg' with h1 | h1
  ·
    have hsqa : InSq D a := by
      have h2 := hsq3.conj hN g'
      rwa [h1] at h2
    have hsqz : InSq D z := by
      have h2 := hsqa.conj hN g⁻¹
      rwa [show g⁻¹ * a * g⁻¹⁻¹ = z by rw [← hg]; group] at h2
    obtain ⟨r, hr, s, hs, hrs, hrsc, hzrs⟩ := hsqz
    exact hz2 r hr s hs hrs hrsc hzrs
  ·
    have hsqaz : InSq D (a * z) := by
      have h2 := hsq3.conj hN g'
      rwa [h1] at h2
    obtain ⟨x, hx, y, hy, hxy, hcxy, hazxy⟩ := hsqaz
    have hcaz : Commute c (a * z) := hac.symm.mul_right hcΓ.2
    have hγaz : Commute (γ : G) (a * z) := haγ.symm.mul_right hγL.2
    rw [hazxy] at hcaz hγaz
    have hcx := ((hD.commute_mul_iff hx hy hcΓ.1 hxy hcxy).mp hcaz).1
    have hγx := ((hD.commute_mul_iff hx hy hγL.1 hxy hcxy).mp hγaz).1
    have hreach : Reach D (c' : G) (γ : G) :=
      reach_trans (reach_of_commute hcΓ.1 hx hcx) (reach_of_commute hx hγL.1 hγx.symm)
    have hcw := reach_of_spread hD hN ρ hρ hinj hcomm hcL hρc hγL (by rw [hργ]; exact hγA)
      hreach (y := ⟨w, mem_localGroup_of_mem hw'⟩) hw'
    exact huw (reach_trans huc hcw)

theorem lemma316L24Input : Lemma316L24Input := by
  intro G _ _ D hS hrad _ hZ _ _ hnsq u _ w _ v _ htri n hn _ hord huw _ hO2 _ hL
  exact false_of_psl2 hS hrad hZ hnsq htri hn hord huw hO2 hL

theorem theoremOne : TheoremOne :=
  theoremOne_of_lemma316L24 lemma316L24Input

end CFSG.Timmesfeld.Bridge.Asc72

namespace CFSG.CGT.Timmesfeld75


theorem lemma215 : Lemma215Stmt :=
  lemma215_of_lemma316L24 CFSG.Timmesfeld.Bridge.Asc72.lemma316L24Input

end CFSG.CGT.Timmesfeld75
