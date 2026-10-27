module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R3Red
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Abs
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Quot
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4L27Inv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 Ch3E213M E217R3
open CFSG.GorensteinWalter (PSL2)

namespace E217R4

theorem r3Pkg1b7
    (h38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat) : R3Pkg1b7 := by
  intro G _ _ H T M V K hS _ h1 hPSL _ haut
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hS.toHyp2
  have hmp := h.hyp.minParabolic
  have hMH : M ≤ H := hmp.maximal.1.le
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', hDker⟩ :=
    qrcHyp_of_hyp28 h.hyp h.charTwo
  have := hel
  obtain ⟨-, -, -, hKn, hCK, -, ⟨hSB, -, -⟩, -, hEcard, hEO⟩ :=
    H13.QRC.bender_section_setup hS.not_solvable T' hTn hTM' hMH' hmax' hVT' hVM'
  obtain ⟨t₀, ht₀T, -, hK, hc, hd⟩ :=
    exists_paired_of_case1_aux h38 h.hyp hS.mem_cComp hS.eq_sup h1
  set D := kerIn (M.subgroupOf H) (⊤ : Subgroup H) with hD
  set π := QuotientGroup.mk' D with hπ
  set K₁ := barIn M H K with hK₁
  set S := (T' : Subgroup H).map π with hSdef
  rw [hK] at hKn hCK
  obtain ⟨φ⟩ := nonempty_mulEquiv_star hMH K
  obtain ⟨-, F, _, _, hF, ⟨ψ₀⟩⟩ := hPSL
  have hF' : Nat.card F = 7 := by rw [hF, pow_one]
  have hp : Nat.Prime 7 := by norm_num
  have hp8 : 7 % 8 = 1 ∨ 7 % 8 = 7 := Or.inr rfl
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
  obtain ⟨x, hxH, hxV, hxQ, hv02, hv01, hv0T, hv0M, hodd0⟩ := exists_vbar_aux h
  set v₀ := E2P.starMap M H ⟨x, hxH⟩ with hv₀
  set e := starEquiv hMH with he
  set v : ↥H ⧸ D := e.symm v₀ with hv
  have hvπ : v = π ⟨x, hxH⟩ := by
    rw [hv, MulEquiv.symm_apply_eq]
    rfl
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
  have : Fintype F := Fintype.ofFinite F
  have hF7 : Fintype.card F = 7 := by rw [← Nat.card_eq_fintype_card, hF']
  have hL₁ : L27 ↥K₁ := L27.of_mulEquiv θ (l27_psl hF7)
  let θ₂ : ↥K₂ ≃* PSL2 F :=
    (K₁.equivMapOfInjective (MulAut.conj (π t₀)).toMonoidHom
      (MulAut.conj (π t₀)).injective).symm.trans θ
  have hL₂ : L27 ↥K₂ := L27.of_mulEquiv θ₂ (l27_psl hF7)
  obtain ⟨Ā, T₀, hA9, hT₀S, hT₀N, hirr, -, hvT₀, hvinv⟩ := exists_pair_of_swap hSsyl hNn hc hd hL₁
    hL₂ hK₂ htS hvS hv2 hv1 (hvz ▸ hzY.2)
  have hDeq : D = (pCoreOf 2 H).subgroupOf H :=
    (kerIn_subgroupOf_top_eq hMH).trans (by rw [h1.1])
  have hker : ∀ y : ↥H, π y = 1 ↔ (y : G) ∈ pCoreOf 2 H := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hDeq, Subgroup.mem_subgroupOf]
  have hVT₀b : (V.subgroupOf H).map π ≤ T₀ := by
    rintro _ ⟨y, hy, rfl⟩
    rcases E2.forall_mem_or_mul_mem_of_relIndex_eq_two h.hyp.elem h.two hxV hxQ (y : G) hy
      with hq | hq
    · rw [(hker y).2 hq.2]
      exact T₀.one_mem
    · have h3 : π ⟨x, hxH⟩ * π y = 1 := by
        rw [← map_mul]
        exact (hker _).2 hq.2
      have h4 : π y = v := by
        rw [eq_inv_of_mul_eq_one_right h3, ← hvπ]
        exact inv_eq_of_mul_eq_one_right hv2
      rw [h4]
      exact hvT₀
  have hST : S = (T.subgroupOf H).map π := by rw [hSdef, hT']
  refine false_of_quotient h.hyp h.charTwo h.q32 h.V16 (D := D) hDeq hA9 (hT₀S.trans hST.le) hT₀N
    hirr hxV hVT₀b fun a ha => ?_
  have := hvinv a ha
  rwa [hvπ] at this

end E217R4

end CFSG.Quasithin
