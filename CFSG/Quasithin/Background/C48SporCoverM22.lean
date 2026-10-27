module

public import CFSG.Quasithin.Background.C48SporCoverM22Z
public import CFSG.Quasithin.Background.C48SporCoverDefs
public import Certificates.Certificate7221

public section

namespace CFSG.Quasithin.C48Cover

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers
  CFSG.Sporadic.Recognition.M22Multiplier CFSG.Sporadic.Recognition.CoverTransfer
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Certificates
  CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M22 CFSG.Quasithin.KGC31.Native CFSG.Blueprint
open scoped commutatorElement

theorem c7221_card :
    Nat.card (Subgroup.closure {g : Equiv.Perm (Fin 22) | g ∈ e8Gen}) = 1344 :=
  Certificates.certificate7221.1

theorem c7221_masks :
    ((e8Gen.zip e8Masks).all fun p => masksOK 22 e8T (toTable p.1) p.2) = true :=
  Certificates.certificate7221.2.1

theorem c7221_stab :
    ∃ S : Subgroup (PresentedGroup {r : FreeGroup (Fin 2) | r ∈ m22Cover.map FreeGroup.mk}),
      (∀ u ∈ e8SubW, PresentedGroup.mk _ (FreeGroup.mk u) ∈ S) ∧
        PresentedGroup.mk _ (FreeGroup.mk m22B11) ∉ S :=
  Certificates.certificate7221.2.2

theorem coe_lift_m22Ab (w : List (Fin 2 × Bool)) :
    ((FreeGroup.lift m22Ab (FreeGroup.mk w) : G₀) : Equiv.Perm (Fin 22)) =
      permAB w := by
  rw [FreeGroup.lift_mk, permAB]
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    fin_cases i <;> cases b <;> rfl

theorem coe_m22Gen (i : Fin 2) :
    ((m22Gen i : G₀) : Equiv.Perm (Fin 22)) = genPerm i := by
  rw [genPerm, tab_eq, m22Gen, coe_lift_m22Ab]

theorem coe_lift_m22Gen (w : List (Fin 2 × Bool)) :
    ((FreeGroup.lift m22Gen (FreeGroup.mk w) : G₀) : Equiv.Perm (Fin 22)) =
      permGen w := by
  rw [FreeGroup.lift_mk, permGen]
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, ih, List.map_cons, List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · simp only [Bool.cond_false, Subgroup.coe_inv, coe_m22Gen, Bool.false_eq_true, ↓reduceIte]
    · simp only [Bool.cond_true, coe_m22Gen, ↓reduceIte]

@[expose] noncomputable def eltGen (w : List ℤ) : G₀ :=
  FreeGroup.lift m22Gen (FreeGroup.mk (m22Word w))

@[expose] noncomputable def e8N : Subgroup G₀ := Subgroup.closure {x | ∃ w ∈ e8NormW, eltGen w = x}

theorem e8Gen_eq : e8Gen = e8NormW.map fun w => ((eltGen w : G₀) : Equiv.Perm (Fin 22)) := by
  simp only [e8Gen, tab_eq, eltGen, coe_lift_m22Gen]

theorem map_e8N : e8N.map NativeSporadic.M22.subtype = Subgroup.closure {g | g ∈ e8Gen} := by
  rw [e8N, MonoidHom.map_closure, e8Gen_eq]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩

theorem card_e8N : Nat.card e8N = 1344 := by
  rw [← c7221_card, ← map_e8N, Subgroup.card_map_of_injective Subtype.val_injective]

theorem mem_eNorm_of_mem_zip
    {w : List ℤ} {mask : List ℕ}
    (h : (((eltGen w : G₀) : Equiv.Perm (Fin 22)), mask) ∈ e8Gen.zip e8Masks) :
    eltGen w ∈ eNorm basis_e8 := by
  have h1 := List.all_eq_true.mp c7221_masks _ h
  have hT := rep_toTable hn22 ((eltGen w : G₀) : Equiv.Perm (Fin 22))
  have h2 := conj_of_masksOK hn22 forall₂_e8 hT h1
  refine mem_eNorm basis_e8 (Matrix.of fun r i => maskVec 3 (mask.getD i 0) r)
    fun i => Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  refine (h2 i).trans ?_
  exact (map_eElt (v := vE8) NativeSporadic.M22.subtype _).symm

theorem eltGen_mem_eNorm
    {w : List ℤ} (hw : w ∈ e8NormW) : eltGen w ∈ eNorm basis_e8 := by
  simp only [e8NormW, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact mem_eNorm_of_mem_zip (mask := [1, 4, 2]) (by rw [e8Gen_eq]; simp [e8NormW, e8Masks])
  · exact mem_eNorm_of_mem_zip (mask := [5, 3, 7]) (by rw [e8Gen_eq]; simp [e8NormW, e8Masks])

theorem e8N_eq :
    e8N = eNorm basis_e8 := by
  have hle : e8N ≤ eNorm basis_e8 := by
    rw [e8N, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact eltGen_mem_eNorm hw
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_eNorm_e8, card_e8N])

theorem commutatorElement_mul_center {Γ : Type*} [Group Γ] {c₁ c₂ : Γ}
    (h₁ : c₁ ∈ Subgroup.center Γ) (h₂ : c₂ ∈ Subgroup.center Γ) (u v : Γ) :
    ⁅c₁ * u, c₂ * v⁆ = ⁅u, v⁆ := by
  have k1 : ∀ g, c₁ * g * c₁⁻¹ = g := fun g => by
    rw [(Subgroup.mem_center_iff.mp h₁ g).symm, mul_inv_cancel_right]
  have k2 : ∀ g, c₂ * g * c₂⁻¹ = g := fun g => by
    rw [(Subgroup.mem_center_iff.mp h₂ g).symm, mul_inv_cancel_right]
  have k2' : u * c₂ * u⁻¹ = c₂ := by
    rw [Subgroup.mem_center_iff.mp h₂ u, mul_inv_cancel_right]
  have s1 : ⁅c₁ * u, c₂ * v⁆ = ⁅u, c₂ * v⁆ := by
    rw [commutatorElement_def, commutatorElement_def, mul_inv_rev,
      show c₁ * u * (c₂ * v) * (u⁻¹ * c₁⁻¹) = c₁ * (u * (c₂ * v) * u⁻¹) * c₁⁻¹ by group, k1]
  have s2 : ⁅u, c₂ * v⁆ = ⁅u, v⁆ := by
    rw [commutatorElement_def, commutatorElement_def,
      show u * (c₂ * v) * u⁻¹ * (c₂ * v)⁻¹ = (u * c₂ * u⁻¹) * (u * v * u⁻¹ * v⁻¹) * c₂⁻¹ by
        group, k2', k2]
  rw [s1, s2]

theorem commutator_inf_center_eq_bot
    {Q : Type} [Group Q]
    [Group.IsPerfect Q] (q : Q →* G₀) (hq : Function.Surjective q)
    (hker : q.ker = Subgroup.center Q) (hZ2 : Nat.card (Subgroup.center Q) = 2) (g : G₀) :
    ⁅((eNorm basis_e8).map (MulAut.conj g).toMonoidHom).comap q,
      ((eNorm basis_e8).map (MulAut.conj g).toMonoidHom).comap q⁆ ⊓ Subgroup.center Q = ⊥ := by
  classical
  have hh := m22TabCheck_eq_true
  have hP : IsPresentation m22Gen (wordSet m22Rels) := isPresentation_m22Gen hh card_PG_m22Rels_le
  have hwg : ∀ i, FreeGroup.lift m22Gen (m22CommW i) = m22Gen i := lift_m22CommWord hh
  set π := coverMap hP hwg with hπ
  have hcomm : ∀ i, m22CommW i ∈ commutator (FreeGroup (Fin 2)) :=
    fun i => mk_commWords_mem_commutator _
  obtain ⟨Φ, -, hΦ⟩ := exists_surjective_lift hP hcomm hwg q hq hker.le
  have hΦq : ∀ x, q (Φ x) = π x := fun x => by rw [← MonoidHom.comp_apply, hΦ]
  set ζ : M22Cover := PresentedGroup.mk _ (FreeGroup.mk m22B11) with hζ
  have hζZ : ζ ∈ Subgroup.center M22Cover :=
    mk_mem_center m22CommW (List.mem_map_of_mem m22B11_mem)
  have hζπ : π ζ = 1 := by rw [hπ, hζ, coverMap_mk]; exact lift_m22B11 hh
  have hkerπ : π.ker = Subgroup.zpowers ζ := by
    obtain ⟨hw', -, hcard⟩ :=
      CFSG.Sporadic.Recognition.CoverCyclic.cover_ker_cyclic_of_bounds
        hP m22Comm (lift_m22CommWord hh) (N := 12) (lift_m22B11 hh)
        cover_bounds (by rw [CFSG.Sporadic.Mathieu.card_M22])
    have hcard' : Nat.card π.ker = 12 := hcard
    have key : ∀ T : Set (FreeGroup (Fin 2)), wordSet m22Cover = T →
        12 ∣ orderOf (PresentedGroup.mk T (FreeGroup.mk m22B11)) := by
      rintro T rfl
      exact cover_bounds.2.2
    have hord : 12 ∣ orderOf ζ := key _ (coverRelators_wordSet m22Rels m22CommWord).symm
    have hζk : ζ ∈ π.ker := hζπ
    have hord2 : orderOf ζ ∣ 12 := by
      rw [← Subgroup.orderOf_mk ζ hζk, ← hcard']
      exact orderOf_dvd_natCard _
    have hle : Subgroup.zpowers ζ ≤ π.ker := by
      rw [Subgroup.zpowers_le]
      exact hζk
    have : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hcard']; norm_num)
    refine Subgroup.eq_of_le_of_card_ge hle ?_ |>.symm
    rw [hcard', Nat.card_zpowers, Nat.dvd_antisymm hord2 hord]
  have hrels : {r : FreeGroup (Fin 2) | r ∈ m22Cover.map FreeGroup.mk} =
      coverRelators (wordSet m22Rels) m22CommW := (coverRelators_wordSet m22Rels m22CommWord).symm
  have hstab := c7221_stab
  rw [hrels] at hstab
  obtain ⟨S, hSfix, hSmove⟩ := hstab
  have hζS : ζ ∉ S := hSmove
  have hζ2S : ζ * ζ ∈ S := by
    have := hSfix (m22B11 ++ m22B11) (by simp [e8SubW])
    rwa [← FreeGroup.mul_mk, map_mul] at this
  have hπS : eNorm basis_e8 ≤ S.map π := by
    rw [← e8N_eq, e8N, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [e8NormW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨_, hSfix (m22Word [-2, 1, 2, -1, -2, 1, 1]) (by simp [e8SubW]),
        by rw [hπ, coverMap_mk]; rfl⟩
    · refine ⟨_, hSfix (m22Word [1, -2, 1, 2, 2, 2, 1, 2] ++ m22B11) (by simp [e8SubW]), ?_⟩
      rw [hπ, coverMap_mk, ← FreeGroup.mul_mk, map_mul, lift_m22B11 hh, mul_one]
      rfl
  have hΦζ : Φ ζ ∈ Subgroup.center Q := by
    rw [← hker, MonoidHom.mem_ker, hΦq, hζπ]
  have hΦζ2 : Φ ζ * Φ ζ = 1 := by
    have h1 := pow_card_eq_one' (G := ↥(Subgroup.center Q)) (x := ⟨Φ ζ, hΦζ⟩)
    rw [hZ2, sq] at h1
    exact congrArg Subtype.val h1
  obtain ⟨ĝ, hĝ⟩ := coverMap_surjective hP hwg g
  set P := ((eNorm basis_e8).map (MulAut.conj g).toMonoidHom).comap q with hPdef
  have hdec : ∀ x ∈ P, ∃ s ∈ S, ∃ c ∈ Subgroup.center Q, x = c * Φ (ĝ * s * ĝ⁻¹) := by
    intro x hx
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨s, hs, hsn⟩ := hπS hn
    refine ⟨s, hs, x * (Φ (ĝ * s * ĝ⁻¹))⁻¹, ?_, by group⟩
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hΦq, map_mul, map_mul, map_inv, hĝ, hsn,
      ← hnx]
    simp [MulAut.conj_apply]
  have hcen : ∀ s ∈ S, Φ (ĝ * s * ĝ⁻¹) ∈ Subgroup.center Q → Φ (ĝ * s * ĝ⁻¹) = 1 := by
    intro s hs hc
    have h1 : π (ĝ * s * ĝ⁻¹) = 1 := by
      rw [← hΦq, ← MonoidHom.mem_ker, hker]
      exact hc
    have h2 : π s = 1 := by
      rw [map_mul, map_mul, map_inv] at h1
      have := congrArg (fun x => (π ĝ)⁻¹ * x * π ĝ) h1
      simpa [mul_assoc] using this
    have h3 : s ∈ Subgroup.zpowers ζ := by
      rw [← hkerπ, MonoidHom.mem_ker]
      exact h2
    obtain ⟨k, rfl⟩ := h3
    have hc' : ĝ * ζ ^ k * ĝ⁻¹ = ζ ^ k := by
      rw [Subgroup.mem_center_iff.mp (Subgroup.zpow_mem _ hζZ k) ĝ, mul_inv_cancel_right]
    rw [hc']
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · rw [map_zpow, zpow_mul, zpow_two, hΦζ2, one_zpow]
    · exfalso
      apply hζS
      have h5 : ζ ^ (2 * j + 1) * (ζ * ζ) ^ (-j) = ζ := by
        rw [← sq, ← zpow_natCast, ← zpow_mul, ← zpow_add]
        have : (2 * j + 1 + ((2 : ℕ) : ℤ) * -j : ℤ) = 1 := by push_cast; ring
        rw [this, zpow_one]
      rw [← h5]
      exact S.mul_mem hs (S.zpow_mem hζ2S _)
  rw [eq_bot_iff]
  rintro x ⟨hx, hxZ⟩
  have hx' : x ∈ (S.map (MulAut.conj ĝ).toMonoidHom).map Φ := by
    refine (Subgroup.commutator_le.mpr ?_) hx
    intro a ha b hb
    obtain ⟨s, hs, c₁, hc₁, rfl⟩ := hdec a ha
    obtain ⟨t, ht, c₂, hc₂, rfl⟩ := hdec b hb
    have hcomm' : ⁅c₁ * Φ (ĝ * s * ĝ⁻¹), c₂ * Φ (ĝ * t * ĝ⁻¹)⁆ =
        Φ ⁅ĝ * s * ĝ⁻¹, ĝ * t * ĝ⁻¹⁆ := by
      rw [commutatorElement_mul_center hc₁ hc₂, map_commutatorElement]
    rw [hcomm']
    have hst : ⁅s, t⁆ ∈ S := by
      rw [commutatorElement_def]
      exact S.mul_mem (S.mul_mem (S.mul_mem hs ht) (S.inv_mem hs)) (S.inv_mem ht)
    refine Subgroup.mem_map_of_mem Φ ⟨⁅s, t⁆, hst, ?_⟩
    simp [commutatorElement_def, MulAut.conj_apply]
    group
  obtain ⟨y, ⟨s, hs, rfl⟩, rfl⟩ := hx'
  have : (MulAut.conj ĝ).toMonoidHom s = ĝ * s * ĝ⁻¹ := rfl
  rw [this] at hxZ ⊢
  exact hcen s hs hxZ

theorem exists_map_eq_e8
    {X : Type} [Group X] (e : X ≃* G₀) {N : Subgroup X}
    (hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hN2 : ∀ a ∈ N, a * a = 1) (hN8 : Nat.card N = 8)
    {y t : X} (hyN : y ∈ Subgroup.normalizer (N : Set X)) (hy7 : orderOf y = 7) (htN : t ∈ N)
    (hyt : y * t * y⁻¹ ≠ t) :
    ∃ g : G₀, N.map ((MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom) = eSub basis_e8 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hP, hPi⟩ := KGC31.M22.sylow_of_order KGC31.M22.orderOf_x7 (by norm_num)
  obtain ⟨g, hg⟩ := KGC31.exists_conj_mem_of_sylow hP hPi (y := e y) ⟨1, by
    rw [pow_one, ← hy7, ← orderOf_injective e.toMonoidHom e.injective y]
    exact pow_orderOf_eq_one _⟩
  set ψ : X →* KGC31.M22.G₀ := (MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom with hψ
  have hψi : Function.Injective ψ := (MulAut.conj g⁻¹).injective.comp e.injective
  have hψa : ∀ a, ψ a = g⁻¹ * e a * g := fun a => by
    simp [hψ]
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hyt
    group
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact hN2 t htN) ht1
  have hU := KGC31.M22.orbSub_cases7 (y := ψ y) (t := ψ t) (by rw [hψa]; exact hg)
    (by rw [orderOf_injective ψ hψi]; exact ht2)
    (fun h => hyt (hψi (by rwa [map_mul, map_mul, map_inv])))
    (fun j _ => by
      have h1 := hNc t htN _ (conj_pow_mem hyN htN j)
      have h2 := congrArg ψ h1
      simp only [map_mul, map_pow, map_inv] at h2
      rw [inv_pow]
      exact h2)
  rw [← KGC31.orbSub_map] at hU
  refine ⟨g, ?_⟩
  have : Finite ↥N := Nat.finite_of_card_ne_zero (by rw [hN8]; norm_num)
  have hle : KGC31.orbSub y t ≤ N := KGC31.orbSub_le hyN htN
  have hcard : Nat.card (KGC31.orbSub y t) = 8 := by
    rw [← Subgroup.card_map_of_injective hψi, hU, card_eSub]
    norm_num
  have heq : KGC31.orbSub y t = N := Subgroup.eq_of_le_of_card_ge hle (by rw [hN8, hcard])
  rw [← heq]
  exact hU

theorem c48SporCoverM22_holds
    {G : Type} [Group G] [Finite G] : C48SporCoverM22 G := by
  intro H R M L V K h hK hc h3 hpsl
  classical
  have hle2 := card_center_le_two_of_m22 H R M L V K h hK hc h3 hpsl
  obtain ⟨hLM₀, -, hM₀K, hMK, hZ, -⟩ := hc
  set M₀ := conjClosure L M with hM₀
  rw [hLM₀] at hpsl
  have hcard168 : Nat.card (ModO2 M₀) = 168 := GoldS146R.card_of_isPSL_three_two hpsl
  have hback : V.subgroupOf K ⊓ Subgroup.center ↥K = ⊥ → V ⊓ centerOf K = ⊥ := by
    intro hcore
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxK, hxC⟩
    have hx1 : (⟨x, hxK⟩ : ↥K) ∈ V.subgroupOf K ⊓ Subgroup.center ↥K :=
      ⟨hxV, Subgroup.mem_center_iff.mpr fun g => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp hxC g g.2)⟩
    rw [hcore, Subgroup.mem_bot] at hx1
    exact congrArg Subtype.val hx1
  apply hback
  rcases Nat.lt_or_ge (Nat.card (Subgroup.center ↥K)) 2 with h1 | h2
  · have hZ1 : Subgroup.center ↥K = ⊥ := Subgroup.eq_bot_of_card_le _ (by omega)
    rw [hZ1, inf_bot_eq]
  have hZ2 : Nat.card (Subgroup.center ↥K) = 2 := le_antisymm hle2 h2
  obtain ⟨hs, hext | hext | hext⟩ := h3
  · exfalso
    obtain ⟨Y, _, hY, hd⟩ :=
      C48Spor.card_modO2_dvd_of_isExt hM₀K hZ (fun h => C48Spor.isPGroup_of_isE2 h) hext
    rw [C48Spor.card_of_isPSL_two_two_two hY, hcard168] at hd
    norm_num at hd
  · exfalso
    obtain ⟨Y, _, hY, hd⟩ :=
      C48Spor.card_modO2_dvd_of_isExt hM₀K hZ (fun h => C48Spor.isPGroup_of_isE2 h) hext
    rw [C48Spor.card_of_isAlt_six hY, hcard168] at hd
    norm_num at hd
  obtain ⟨e⟩ := hs
  let e' : ↥K ⧸ Subgroup.center ↥K ≃* KGC31.M22.G₀ := e
  have hKperf : commutator ↥K = ⊤ := hK.2.2.1
  have : Group.IsPerfect ↥K := Group.isPerfect_def.mpr hKperf
  set Mb := imageModCenter K M₀ with hMb
  obtain ⟨N₀, hN₀, ⟨eN⟩, hY⟩ := hext
  have hYs : IsSimpleGroup (↥Mb ⧸ N₀) := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1 hY).2
  have hcardY : Nat.card (↥Mb ⧸ N₀) = 168 := GoldS146R.card_of_isPSL_three_two hY
  have hq : C31Spor.QuasiNoTwo (↥Mb ⧸ N₀) := C31Spor.quasiNoTwo_L32 hY
  have hN₀8 : Nat.card ↥N₀ = 8 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_eq_fintype_card]
    rfl
  have hN₀2 : ∀ n ∈ N₀, n * n = 1 := by
    intro n hn
    have h1 : eN ⟨n, hn⟩ * eN ⟨n, hn⟩ = 1 := e8_mul_self _
    rw [← map_mul, MulEquiv.map_eq_one_iff] at h1
    exact congrArg Subtype.val h1
  have hN₀c : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a := by
    intro a ha b hb
    have h1 : eN ⟨a, ha⟩ * eN ⟨b, hb⟩ = eN ⟨b, hb⟩ * eN ⟨a, ha⟩ := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (eN.injective h1)
  have hN₀p : IsPGroup 2 ↥N₀ := fun n =>
    ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hN₀2 _ n.2)⟩
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using h.V_elem.2 x x.2)⟩
  have hVO₂ : V ≤ pCoreOf 2 M₀ :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V M₀ h.V_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer h.V_le).mpr
        (C48Spor.M0_le_normalizer_V h)) hV2
  obtain ⟨y₀, hy₀7, t₀, ht₀, hyt₀⟩ := exists_order_seven_moving hM₀K hVO₂ h.V_le h.V_comm h.V_ne
    hN₀p hN₀c hYs hq (by rw [hcardY]; norm_num)
  set N : Subgroup (↥K ⧸ Subgroup.center ↥K) := N₀.map Mb.subtype with hN
  have hBN : Mb ≤ Subgroup.normalizer (N : Set (↥K ⧸ Subgroup.center ↥K)) := by
    have h1 := Subgroup.le_normalizer_map (H := N₀) Mb.subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr hN₀, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
  have hNc : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hN₀c a ha b hb)
  have hN2 : ∀ a ∈ N, a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hN₀2 a ha)
  have hN8 : Nat.card N = 8 := by
    rw [← Nat.card_congr (N₀.equivMapOfInjective Mb.subtype Mb.subtype_injective).toEquiv,
      hN₀8]
  have hy7 : orderOf (y₀ : ↥K ⧸ Subgroup.center ↥K) = 7 := by
    rw [Subgroup.orderOf_coe]; exact hy₀7
  have htN : (t₀ : ↥K ⧸ Subgroup.center ↥K) ∈ N := ⟨t₀, ht₀, rfl⟩
  have hyt : (y₀ : ↥K ⧸ Subgroup.center ↥K) * t₀ * (y₀ : ↥K ⧸ Subgroup.center ↥K)⁻¹ ≠ t₀ :=
    fun h1 => hyt₀ (Subtype.ext h1)
  obtain ⟨g, hg⟩ := exists_map_eq_e8 e' hNc hN2 hN8 (hBN y₀.2) hy7 htN hyt
  set ψ : (↥K ⧸ Subgroup.center ↥K) ≃* KGC31.M22.G₀ := e'.trans (MulAut.conj g⁻¹) with hψ
  have hψN : N.map ψ.toMonoidHom = eSub basis_e8 := hg
  have hMbψ : ∀ b ∈ Mb, ψ b ∈ eNorm basis_e8 := by
    intro b hb
    have h1 := Subgroup.mem_map_of_mem ψ.toMonoidHom (hBN hb)
    rwa [Subgroup.map_equiv_normalizer_eq, hψN] at h1
  set q : ↥K →* KGC31.M22.G₀ := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
    with hqdef
  have hq' : Function.Surjective q :=
    e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hqdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hcore := commutator_inf_center_eq_bot q hq' hqker hZ2 g
  set P := ((eNorm basis_e8).map (MulAut.conj g).toMonoidHom).comap q with hPdef
  have hM₀P : M₀.subgroupOf K ≤ P := by
    intro m hm
    have hmb : QuotientGroup.mk' (Subgroup.center ↥K) m ∈ Mb := Subgroup.mem_map_of_mem _ hm
    refine ⟨ψ (QuotientGroup.mk' (Subgroup.center ↥K) m), hMbψ _ hmb, ?_⟩
    simp only [hψ, hqdef, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulEquiv.trans_apply,
      MonoidHom.comp_apply]
    group
  have hVM₀ : V.subgroupOf K ≤ M₀.subgroupOf K := fun v hv => h.V_le hv
  have hVc : ⁅V.subgroupOf K, M₀.subgroupOf K⁆ = V.subgroupOf K := by
    rw [← C48Spor.commutator_subgroupOf_of_le (h.V_le.trans hM₀K) hM₀K, h.V_comm]
  have hVP : V.subgroupOf K ≤ ⁅P, P⁆ := by
    rw [← hVc]
    exact Subgroup.commutator_mono (hVM₀.trans hM₀P) hM₀P
  rw [eq_bot_iff, ← hcore]
  exact inf_le_inf_right _ hVP

theorem c48SporCoverFact_of_ru
    {G : Type} [Group G]
    [Finite G] (hRu : C48SporCoverRu G) : C48SporCoverFact G :=
  c48SporCoverFact_of c48SporCoverM22_holds hRu

end CFSG.Quasithin.C48Cover
