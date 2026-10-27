module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Pair
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Star
public import CFSG.Quasithin.Vol2.GoldschmidtE217Klein
public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Rigid
public import CFSG.Quasithin.Vol2.Ch3E213MP3E
public import CFSG.Quasithin.Background.E2TwoProofFam

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)
open CFSG.GorensteinWalter (PSL2)

namespace E217R3

variable {G : Type} [Group G] [Finite G]

theorem eq_seven_of_oddPaired
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) {H T M V K : Subgroup G}
    (h : Hyp2 H T M V) (hns : ¬ Group.IsSolvable H) (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (h1 : Case1 H T M K) {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    (hPSL : IsPSL 2 p 1 ↥(E2.star M H K))
    (haut : 8 < E2.autCard (E2.star M H T) (E2.star M H K)) : p = 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmp := h.hyp.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', hDker⟩ :=
    qrcHyp_of_hyp28 h.hyp h.charTwo
  have := hel
  obtain ⟨-, -, -, hKn, hCK, -, ⟨hSB, -, -⟩, -, hEcard, hEO⟩ :=
    H13.QRC.bender_section_setup hns T' hTn hTM' hMH' hmax' hVT' hVM'
  obtain ⟨t₀, ht₀T, -, hK, hc, hd⟩ := exists_paired_of_case1_aux h38 h.hyp hKc hHK h1
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hD
  set π := QuotientGroup.mk' D with hπ
  set K₁ := barIn M H K with hK₁
  set S := (T' : Subgroup H).map π with hSdef
  rw [hK] at hKn hCK
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  obtain ⟨-, F, _, _, hF, ⟨ψ₀⟩⟩ := hPSL
  have hF' : Nat.card F = p := by rw [hF, pow_one]
  set θ : K₁ ≃* PSL2 F := φ.trans (ψ₀.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm) with hθ
  have := P3.isSimpleGroup_of hp hp8 hF' θ
  have hS2 : IsPGroup 2 S := T'.isPGroup'.map π
  have hSsyl : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, hS2, ?_⟩
    show ¬ 2 ∣ S.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    have h := (T'.mapSurjective (QuotientGroup.mk'_surjective D)).not_dvd_index
    rwa [Sylow.coe_mapSurjective] at h
  have htS : π t₀ ∈ S := ⟨t₀, hT' ▸ ht₀T, rfl⟩
  have haut' : 8 < E2.autCard S K₁ := by
    have hST : S = barIn M H T := by rw [hSdef, hT']; rfl
    rw [← P3.autCard_map (starEquiv hMH), hST, hK₁, map_barIn_starEquiv, map_barIn_starEquiv]
    exact haut
  set K₂ := K₁.map (MulAut.conj (π t₀)).toMonoidHom with hK₂
  obtain ⟨v₀, hv02, hv01, hv0T, hv0M, hodd0⟩ := exists_vbar h
  set e := starEquiv hMH with he
  set v : ↥H ⧸ D := e.symm v₀ with hv
  have hv2 : v * v = 1 := by
    rw [hv, ← map_mul, hv02, map_one]
  have hv1 : v ≠ 1 := fun h' => hv01 (by
    have := congrArg e h'
    rw [hv, MulEquiv.apply_symm_apply, map_one] at this
    exact this)
  have hSstar : S.map e.toMonoidHom = E2.star M H T := by
    have hST : S = barIn M H T := by rw [hSdef, hT']; rfl
    rw [hST]
    exact map_barIn_starEquiv hMH T
  have hStarTM : E2.star M H T ≤ E2.star M H M :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hmp.le)
  have hvS : ∀ s ∈ S, s * v = v * s := by
    intro s hs
    have hes : e s ∈ E2.star M H M := hStarTM (hSstar ▸ Subgroup.mem_map_of_mem _ hs)
    have := hv0M (e s) hes
    apply e.injective
    rw [map_mul, map_mul, hv, MulEquiv.apply_symm_apply]
    exact this
  have hodd : OddCube v := hodd0.map e.symm
  have hp7 : 7 ≤ p := P3.seven_le hp hp8
  have hq5 : 5 ≤ Nat.card F := by rw [hF']; omega
  have hF2 : ringChar F ≠ 2 := by
    intro h2
    have : CharP F 2 := h2 ▸ ringChar.charP F
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨n, hp2, hn⟩ := FiniteField.card F 2
    have h3 : p = 2 ^ (n : ℕ) := by rw [← hF', Nat.card_eq_fintype_card, hn]
    have h4 : 2 ∣ p := h3 ▸ dvd_pow_self 2 n.ne_zero
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h4
    omega
  have key : ∀ (A : Subgroup (↥H ⧸ D)) (θA : ↥A ≃* PSL2 F) (a b : ↥H ⧸ D), a ∈ A → a ≠ 1 →
      a * a = 1 → b * b = 1 → (∀ g ∈ A, b * g = g * b) → OddCube (a * b) → p = 7 := by
    intro A θA a b haA ha1 ha2 hb2 hbA hOdd
    have hOA : OddCube (⟨a, haA⟩ : ↥A) :=
      OddCube.of_subgroup haA (OddCube.of_component haA hb2 hbA hOdd)
    have hO' := hOA.map θA
    have hne : θA ⟨a, haA⟩ ≠ 1 := fun h' => ha1 (by
      have := θA.injective (h'.trans (map_one θA).symm)
      exact congrArg Subtype.val this)
    have hsq : θA ⟨a, haA⟩ * θA ⟨a, haA⟩ = 1 := by
      rw [← map_mul, show (⟨a, haA⟩ : ↥A) * ⟨a, haA⟩ = 1 from Subtype.ext ha2, map_one]
    have h57 := card_eq_five_or_seven hF2 hq5 hne hsq hO'
    rw [hF'] at h57
    omega
  have hNn : (K₁ ⊔ K₂).Normal := hKn
  obtain ⟨u, hu2, hu1, huN⟩ : ∃ u : ↥H ⧸ D, u * u = 1 ∧ u ≠ 1 ∧ u ∈ K₁ ⊔ K₂ := by
    set w := CFSG.PSL2Table.splitWeyl F with hw
    have hw1 : w ≠ 1 := fun h' => CFSG.PSL2Table.splitWeyl_not_mem
      (h' ▸ (CFSG.PSL2Table.splitTorus F).one_mem)
    refine ⟨((θ.symm w : ↥K₁) : ↥H ⧸ D), ?_, ?_, Subgroup.mem_sup_left (θ.symm w).2⟩
    · have : (θ.symm w) * (θ.symm w) = 1 := by
        rw [← map_mul, CFSG.PSL2Table.splitWeyl_mul_self, map_one]
      exact congrArg Subtype.val this
    · intro h'
      apply hw1
      have : θ.symm w = 1 := Subtype.ext h'
      simpa using congrArg θ this
  have hY : S ⊓ (K₁ ⊔ K₂) ≠ ⊥ := by
    have hu2g : IsPGroup 2 (Subgroup.zpowers u) := fun x => ⟨1, Subtype.ext (by
      rcases P3.eq_one_or_eq_of_mem_zpowers hu2 x.2 with h' | h'
      · simp [h']
      · simp [h', pow_two, hu2])⟩
    obtain ⟨S', hS', huS'⟩ := exists_isSylowTwoOf_ge hu2g (le_top : Subgroup.zpowers u ≤ ⊤)
    obtain ⟨g, -, hg⟩ := isSylowTwoOf_exists_conj hSsyl hS'
    have huS : u ∈ B6.conjSub g S := hg ▸ huS' (Subgroup.mem_zpowers u)
    rw [B6.mem_conjSub] at huS
    have hmem : g⁻¹ * u * g ∈ S ⊓ (K₁ ⊔ K₂) :=
      ⟨huS, by simpa using hNn.conj_mem u huN g⁻¹⟩
    refine (Subgroup.ne_bot_iff_exists_ne_one).2 ⟨⟨g⁻¹ * u * g, hmem⟩, fun h' => hu1 ?_⟩
    have h'' : g⁻¹ * u * g = 1 := congrArg Subtype.val h'
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [h'']; group
  obtain ⟨z, hzY, hz2o, hzS⟩ := exists_involution_mem_center_of_normal hS2
    (inf_le_left : S ⊓ (K₁ ⊔ K₂) ≤ S)
    (fun t ht y hy => ⟨S.mul_mem (S.mul_mem ht hy.1) (S.inv_mem ht), hKn.conj_mem y hy.2 t⟩) hY
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2o, pow_two] at this
  have hz1 : z ≠ 1 := fun h' => by
    rw [h', orderOf_one] at hz2o
    omega
  have hvz : v = z := by
    by_contra hne
    have hzv : v * z = z * v := (hvS z hzY.1).symm
    set E : Subgroup (↥H ⧸ D) := Subgroup.closure ({v, z} : Set (↥H ⧸ D)) with hE
    have hSc : ∀ s ∈ S, ∀ x ∈ E, s * x = x * s := fun s hs x hx =>
      commute_closure hv2 hz2 hzv (hvS s hs) (hzS s hs) x hx
    have hSE : S ≤ Subgroup.normalizer (E : Set (↥H ⧸ D)) :=
      (show S ≤ Subgroup.centralizer (E : Set (↥H ⧸ D)) from fun s hs =>
        Subgroup.mem_centralizer_iff.2 fun x hx => (hSc s hs x hx).symm).trans
        (Subgroup.centralizer_le_normalizer _)
    have hE4 : 4 ≤ Nat.card E := four_le_card_closure hv2 hz2 hv1 hz1 hne
    obtain ⟨-, a, haE, haC, hEa⟩ := P3.exists_eq_sup hp hp8 hF' θ hc hd hKn hCK hSsyl htS rfl hSE
      (closure_comm hv2 hz2 hzv) (closure_sq hv2 hz2 hzv) hE4 haut'
    have hA : E ⊓ Subgroup.centralizer (K₁ : Set (↥H ⧸ D)) ≠ ⊥ := by
      intro hA
      rw [hA, sup_bot_eq] at hEa
      have ha2 : a * a = 1 := closure_sq hv2 hz2 hzv a haE
      have hsub : (E : Set (↥H ⧸ D)) ⊆ ({1, a} : Set (↥H ⧸ D)) := by
        intro x hx
        have hx' : x ∈ Subgroup.zpowers a := hEa ▸ hx
        rcases P3.eq_one_or_eq_of_mem_zpowers ha2 hx' with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
      have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h3 : ({1, a} : Set (↥H ⧸ D)).ncard ≤ 2 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        rw [Set.ncard_singleton]
      have h4 : Nat.card ↥E = (E : Set (↥H ⧸ D)).ncard := Nat.card_coe_set_eq (E : Set (↥H ⧸ D))
      omega
    obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hA
    have hbE : (b : ↥H ⧸ D) ∈ E := (Subgroup.mem_inf.1 b.2).1
    have hbC : (b : ↥H ⧸ D) ∈ Subgroup.centralizer (K₁ : Set (↥H ⧸ D)) :=
      (Subgroup.mem_inf.1 b.2).2
    have hbt : (π t₀) * b = b * (π t₀) := hSc (π t₀) htS b hbE
    have hbK₁ : ∀ k ∈ K₁, k * (b : ↥H ⧸ D) = (b : ↥H ⧸ D) * k :=
      fun k hk => Subgroup.mem_centralizer_iff.1 hbC k hk
    have hbK₂ : ∀ k ∈ K₂, k * (b : ↥H ⧸ D) = (b : ↥H ⧸ D) * k := fun k hk =>
      (commute_of_mem_map_conj hbt.symm (fun k hk => (hbK₁ k hk).symm) k hk).symm
    refine hb1 (Subtype.ext ?_)
    show (b : ↥H ⧸ D) = 1
    refine hCK b fun k hk => ?_
    have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({(b : ↥H ⧸ D)} : Set (↥H ⧸ D)) :=
      sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hbK₁ k hk))
        (fun k hk => Subgroup.mem_centralizer_singleton_iff.2 (hbK₂ k hk))
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hk)).symm
  subst hvz
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set (↥H ⧸ D)) :=
    (show K₂ ≤ Subgroup.centralizer (K₁ : Set (↥H ⧸ D)) from fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha b hb).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨k1, hk1, k2, hk2, hk12⟩ := E2P.exists_mul_of_mem_sup_of_le_normalizer' hK₂N hzY.2
  have hk2K₁ : ∀ g ∈ K₁, k2 * g = g * k2 := fun g hg => (hc g hg k2 hk2).symm
  have hk1K₂ : ∀ g ∈ K₂, k1 * g = g * k1 := fun g hg => hc k1 hk1 g hg
  have hsq : k1 * k1 = 1 ∧ k2 * k2 = 1 := by
    have h12 : (k1 * k1) * (k2 * k2) = 1 := by
      calc (k1 * k1) * (k2 * k2) = (k1 * k2) * (k1 * k2) := by
            calc (k1 * k1) * (k2 * k2) = k1 * (k1 * k2) * k2 := by group
              _ = k1 * (k2 * k1) * k2 := by rw [hc k1 hk1 k2 hk2]
              _ = (k1 * k2) * (k1 * k2) := by group
        _ = 1 := by rw [hk12]; exact hz2
    have hc1 : k1 * k1 ∈ K₁ := K₁.mul_mem hk1 hk1
    have hc2 : k1 * k1 ∈ K₂ := by
      have : k1 * k1 = (k2 * k2)⁻¹ := eq_inv_of_mul_eq_one_left h12
      rw [this]
      exact K₂.inv_mem (K₂.mul_mem hk2 hk2)
    have : k1 * k1 = 1 := by
      have := hd ▸ (Subgroup.mem_inf.2 ⟨hc1, hc2⟩ : k1 * k1 ∈ K₁ ⊓ K₂)
      simpa using this
    refine ⟨this, ?_⟩
    rw [this, one_mul] at h12
    exact h12
  by_cases hk1one : k1 = 1
  ·
    have hk21 : k2 ≠ 1 := fun h' => hv1 (by rw [← hk12, hk1one, h', one_mul])
    let θ₂ : ↥K₂ ≃* PSL2 F :=
      (K₁.equivMapOfInjective (MulAut.conj (π t₀)).toMonoidHom
        (MulAut.conj (π t₀)).injective).symm.trans θ
    refine key K₂ θ₂ k2 k1 hk2 hk21 hsq.2 hsq.1 hk1K₂ ?_
    rw [hk1one, mul_one]
    rw [hk1one, one_mul] at hk12
    rw [hk12]
    exact hodd
  · exact key K₁ θ k1 k2 hk1 hk1one hsq.1 hsq.2 hk2K₁ (by rw [hk12]; exact hodd)

end E217R3

end CFSG.Quasithin
