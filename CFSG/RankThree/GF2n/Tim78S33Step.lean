module

public import CFSG.RankThree.GF2n.Tim78S33Gold
public import CFSG.RankThree.GF2n.Tim78S31

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

namespace NCPair

variable {U V : Subgroup G} (P : NCPair U V) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)
include P hCen hU

theorem mem_omega_of_swap' {y x : G} (hy2 : y * y = 1) (hyV : conjSubgroup y U = V)
    (hx : x ∈ U ⊔ V)
    (hyC₀ : ∀ c ∈ PartTwo.omegaOneSub (conjSubgroup x U), y * c = c * y) {n : G}
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) (hc : y * n = n * y) :
    n ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  classical
  set N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V with hN
  set K : Subgroup G := N ⊓ Subgroup.centralizer ({y} : Set G) with hK
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hCK : PartTwo.omegaOneSub (conjSubgroup x U) ≤ K := fun c hc' =>
    Subgroup.mem_inf.mpr ⟨P.omega_conj_le_N hCen hU hx hc',
      Subgroup.mem_centralizer_singleton_iff.mpr (hyC₀ c hc').symm⟩
  have hUV : U ⊓ V = ⊥ := P.setup.inf_eq_bot P.ne
  have hsurj : ∀ k ∈ K, ∃ u ∈ PartTwo.omegaOneSub U, k = u * (y * u * y⁻¹) := by
    intro k hk
    obtain ⟨hkN, hkC⟩ := Subgroup.mem_inf.mp hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hkC
    obtain ⟨u, hu, v, hv, rfl⟩ := P.exists_mul hCen hU hkN
    have hu' := (P.conj_omega_of_swap hy2 hyV).1 hu
    have hv' := (P.conj_omega_of_swap hy2 hyV).2 hv
    have he : u * v = (y * v * y⁻¹) * (y * u * y⁻¹) := by
      calc u * v = (u * v * y) * y⁻¹ := by group
        _ = y * (u * v) * y⁻¹ := by rw [hkC]
        _ = (y * u * y⁻¹) * (y * v * y⁻¹) := by group
        _ = (y * v * y⁻¹) * (y * u * y⁻¹) := P.comm_N hCen hU (Subgroup.mem_sup_right hu')
            (Subgroup.mem_sup_left hv')
    have hw : (y * v * y⁻¹)⁻¹ * u ∈ U ⊓ V := by
      refine Subgroup.mem_inf.mpr ⟨U.mul_mem (U.inv_mem (PartTwo.omegaOneSub_le _ hv'))
        (PartTwo.omegaOneSub_le _ hu), ?_⟩
      have : (y * v * y⁻¹)⁻¹ * u = (y * u * y⁻¹) * v⁻¹ := by
        calc (y * v * y⁻¹)⁻¹ * u = (y * v * y⁻¹)⁻¹ * (u * v) * v⁻¹ := by group
          _ = (y * v * y⁻¹)⁻¹ * ((y * v * y⁻¹) * (y * u * y⁻¹)) * v⁻¹ := by rw [he]
          _ = (y * u * y⁻¹) * v⁻¹ := by group
      rw [this]
      exact V.mul_mem (PartTwo.omegaOneSub_le _ hu') (V.inv_mem (PartTwo.omegaOneSub_le _ hv))
    rw [hUV, Subgroup.mem_bot, inv_mul_eq_one] at hw
    refine ⟨u, hu, ?_⟩
    have hvu : v = y * u * y⁻¹ := by
      calc v = y⁻¹ * (y * v * y⁻¹) * y := by group
        _ = y⁻¹ * u * y := by rw [hw]
        _ = y * u * y⁻¹ := by rw [hyinv]
    rw [hvu]
  have hcard : Nat.card K ≤ Nat.card (PartTwo.omegaOneSub U) := by
    let f : ↥(PartTwo.omegaOneSub U) → ↥K := fun u => ⟨(u : G) * (y * u * y⁻¹), by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left u.2)
        (Subgroup.mem_sup_right ((P.conj_omega_of_swap hy2 hyV).1 u.2)), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := P.comm_N hCen hU (Subgroup.mem_sup_left u.2)
        (Subgroup.mem_sup_right ((P.conj_omega_of_swap hy2 hyV).1 u.2))
      calc (u : G) * (y * u * y⁻¹) * y = (y * u * y⁻¹) * u * y := by rw [h1]
        _ = y * ((u : G) * (y * u * y⁻¹)) := by rw [hyinv]; group⟩
    refine Nat.card_le_card_of_surjective f fun k => ?_
    obtain ⟨u, hu, hk⟩ := hsurj k k.2
    exact ⟨⟨u, hu⟩, Subtype.ext hk.symm⟩
  have hKeq : PartTwo.omegaOneSub (conjSubgroup x U) = K := by
    refine Subgroup.eq_of_le_of_card_ge hCK ?_
    rw [omegaOneSub_conj P.setup.comm, card_conjSubgroup]
    exact hcard
  rw [hKeq]
  exact Subgroup.mem_inf.mpr ⟨hn, Subgroup.mem_centralizer_singleton_iff.mpr hc.symm⟩

theorem commutator_mem_omega_of_swap' {y x : G} (hy2 : y * y = 1)
    (hyV : conjSubgroup y U = V) (hx : x ∈ U ⊔ V)
    (hyC₀ : ∀ c ∈ PartTwo.omegaOneSub (conjSubgroup x U), y * c = c * y) {n : G}
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :
    y * n * y⁻¹ * n⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  have hyn := P.conj_N_of_swap hCen hU hy2 hyV hn
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have ht : y * n * y⁻¹ * n⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V :=
    Subgroup.mul_mem _ hyn (Subgroup.inv_mem _ hn)
  refine P.mem_omega_of_swap' hCen hU hy2 hyV hx hyC₀ ht ?_
  have hnn : n⁻¹ = n := inv_eq_of_mul_eq_one_right (P.sq_N hCen hU hn)
  have hc := P.comm_N hCen hU hyn hn
  rw [hyinv] at hc ⊢
  rw [hnn]
  calc y * (y * n * y * n) = (y * y) * n * y * n := by group
    _ = n * y * n := by rw [hy2, one_mul]
    _ = n * (y * n * y) * y := by
        rw [show n * (y * n * y) * y = n * y * n * (y * y) by group, hy2, mul_one]
    _ = (y * n * y) * n * y := by rw [← hc]
    _ = y * n * y * n * y := by group

end NCPair

namespace S3Hyp

variable {M U : Subgroup G} (H : S3Hyp M U)
include H

theorem comm_mem_of_invol (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaComm (PartTwo.omegaOneSub U)) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSM : S ≤ M) (hQS : inSubgroup (pCore 2) M ≤ S) {h : G}
    (hA₀S : conjSubgroup h (PartTwo.omegaOneSub U) ≤ S)
    (hA₀V : conjSubgroup h (PartTwo.omegaOneSub U) ≠ PartTwo.omegaOneSub U) {t : G}
    (htP : t ∈ inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (U : Set G)) (ht2 : t * t = 1) :
    ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U),
      a * t * a⁻¹ * t⁻¹ ∈ PartTwo.omegaOneSub U := by
  classical
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hroot := H.root hCen hU
  have hVTI := hroot.1
  have hVe : ∀ v ∈ PartTwo.omegaOneSub U, v * v = 1 := fun v hv =>
    ((mem_omegaOneSub_iff H.comm).mp hv).2
  have hsc := fun {b g : G} (hb : b ∈ U) (hbg : g * b * g⁻¹ ∈ Subgroup.centralizer (U : Set G)) =>
    H.stronglyClosed hCen hU hS hb hbg
  have hVC : ∀ k w : G, w ∈ conjSubgroup k (PartTwo.omegaOneSub U) →
      w ∈ Subgroup.centralizer (U : Set G) → w ∈ PartTwo.omegaOneSub U := by
    intro k w hw hwC
    have hw' : k⁻¹ * w * k ∈ PartTwo.omegaOneSub U := mem_conjSubgroup.mp hw
    have h1 := hsc (PartTwo.omegaOneSub_le U hw') (g := k)
      (by rw [show k * (k⁻¹ * w * k) * k⁻¹ = w by group]; exact hwC)
    rw [show k * (k⁻¹ * w * k) * k⁻¹ = w by group] at h1
    exact (mem_omegaOneSub_iff H.comm).mpr ⟨h1, mul_self_of_mem_conj hVe hw⟩
  obtain ⟨htQ, htC⟩ := Subgroup.mem_inf.mp htP
  have htU : ∀ u ∈ U, t * u = u * t := fun u hu =>
    (Subgroup.mem_centralizer_iff.mp htC u hu).symm
  have htM : t ∈ M := hQM htQ
  have htS : t ∈ S := hQS htQ
  have hcommP : ∀ m ∈ M, m * t * m⁻¹ * t⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro m hm
    have hmP : m ∈ Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) :=
      mem_normalizer_centralizer (H.normal hm)
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hmP t).mp htC)
      (Subgroup.inv_mem _ htC)
  have hVA : PartTwo.omegaOneSub U ⊓ conjSubgroup h (PartTwo.omegaOneSub U) = ⊥ :=
    inf_conjSubgroup_eq_bot_of_isTI hVTI hA₀V
  by_cases hcase : ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U), a * t = t * a
  · intro a ha
    rw [hcase a ha, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  simp only [not_forall] at hcase
  obtain ⟨a₀, ha₀, hat⟩ := hcase
  have hat' : a₀ * t * a₀⁻¹ * t⁻¹ ≠ 1 := fun h1 => hat (by
    calc a₀ * t = (a₀ * t * a₀⁻¹ * t⁻¹) * (t * a₀) := by group
      _ = t * a₀ := by rw [h1, one_mul])
  set A := conjSubgroup h U with hAdef
  have hA₀ : PartTwo.omegaOneSub A = conjSubgroup h (PartTwo.omegaOneSub U) :=
    omegaOneSub_conj H.comm h
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := Tim78.comm_conj H.comm h
  have hA2 : IsPGroup 2 A := H.two.map (MulAut.conj h).toMonoidHom
  have hATI : IsTI A := isTI_conjSubgroup H.ti h
  have hAexp : ∀ z ∈ A, z ^ 4 = 1 := by
    intro z hz
    have h4 := H.exp _ (mem_conjSubgroup.mp hz)
    rw [show (h⁻¹ * z * h) ^ 4 = h⁻¹ * z ^ 4 * h by
      simpa using conj_pow (a := h⁻¹) (b := z) (i := 4)] at h4
    calc z ^ 4 = h * (h⁻¹ * z ^ 4 * h) * h⁻¹ := by group
      _ = 1 := by rw [h4]; group
  have hAne : ∃ z ∈ A, z ^ 2 ≠ 1 := by
    obtain ⟨u, hu, hu2⟩ := H.exp_ne
    refine ⟨h * u * h⁻¹, ?_, fun h' => hu2 ?_⟩
    · rw [mem_conjSubgroup, show h⁻¹ * (h * u * h⁻¹) * h = u by group]
      exact hu
    · rw [conj_pow] at h'
      calc u ^ 2 = h⁻¹ * (h * u ^ 2 * h⁻¹) * h := by group
        _ = 1 := by rw [h']; group
  have hA₀tS : conjSubgroup t (conjSubgroup h (PartTwo.omegaOneSub U)) ≤ S := by
    intro z hz
    rw [mem_conjSubgroup] at hz
    rw [show z = t * (t⁻¹ * z * t) * t⁻¹ by group]
    exact S.mul_mem (S.mul_mem htS (hA₀S hz)) (S.inv_mem htS)
  have hcommAt : ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U),
      ∀ b ∈ conjSubgroup t (conjSubgroup h (PartTwo.omegaOneSub U)), a * b = b * a := by
    have := hS S hS2 h (t * h) hA₀S (by rw [conjSubgroup_mul]; exact hA₀tS)
    rwa [conjSubgroup_mul] at this
  have hA₀ne : conjSubgroup h (PartTwo.omegaOneSub U) ≠ ⊥ := by
    intro hbot
    apply H.omega_ne_bot
    have := card_conjSubgroup h (PartTwo.omegaOneSub U)
    rw [hbot, Subgroup.card_bot] at this
    exact Subgroup.eq_bot_of_card_eq _ this.symm
  have hsetup : Setup210 A (conjSubgroup t A) :=
    { comm := hAc
      two := hA2
      exp_ne := hAne
      ti := hATI
      conj := ⟨t, rfl⟩
      ne_bot := by
        intro hbot
        apply hA₀ne
        rw [eq_bot_iff, ← hbot]
        intro a ha
        refine Subgroup.mem_inf.mpr ⟨by
          rw [hAdef, mem_conjSubgroup]
          exact PartTwo.omegaOneSub_le U (mem_conjSubgroup.mp ha), ?_⟩
        have hL1 : PartTwo.omegaOneSub (conjSubgroup t A) ≠ ⊥ := by
          rw [omegaOneSub_conj hAc, hA₀]
          intro hb
          apply hA₀ne
          have := card_conjSubgroup t (conjSubgroup h (PartTwo.omegaOneSub U))
          rw [hb, Subgroup.card_bot] at this
          exact Subgroup.eq_bot_of_card_eq _ this.symm
        rw [← mem_normalizer_omega_iff (Tim78.comm_conj hAc t) (isTI_conjSubgroup hATI t) hL1]
        refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr
          fun b hb => (hcommAt a ha b ?_).symm)
        rw [omegaOneSub_conj hAc, hA₀] at hb
        exact hb }
  by_cases hAA : ∀ a ∈ A, ∀ b ∈ conjSubgroup t A, a * b = b * a
  ·
    exfalso
    have hc : conjSubgroup (h⁻¹ * t * h) U ≤ Subgroup.centralizer (U : Set G) := by
      intro z hz
      refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
      have hz' : h * z * h⁻¹ ∈ conjSubgroup t A := by
        rw [hAdef, ← conjSubgroup_mul, mem_conjSubgroup,
          show (t * h)⁻¹ * (h * z * h⁻¹) * (t * h) =
            (h⁻¹ * t * h)⁻¹ * z * (h⁻¹ * t * h) by group]
        exact mem_conjSubgroup.mp hz
      have hu' : h * u * h⁻¹ ∈ A := by
        rw [hAdef, mem_conjSubgroup, show h⁻¹ * (h * u * h⁻¹) * h = u by group]
        exact hu
      have h1 := hAA _ hu' _ hz'
      calc u * z = h⁻¹ * ((h * u * h⁻¹) * (h * z * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * z * h⁻¹) * (h * u * h⁻¹)) * h := by rw [h1]
        _ = z * u := by group
    have hw := H.weaklyClosed hCen hU hS hc
    have htA : conjSubgroup t A = A := by
      rw [hAdef, ← conjSubgroup_mul, show t * h = h * (h⁻¹ * t * h) by group, conjSubgroup_mul,
        hw]
    have htA₀ : ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U),
        t * a * t⁻¹ ∈ conjSubgroup h (PartTwo.omegaOneSub U) := by
      intro a ha
      rw [← hA₀] at ha ⊢
      rw [← htA, omegaOneSub_conj hAc, mem_conjSubgroup,
        show t⁻¹ * (t * a * t⁻¹) * t = a by group]
      exact ha
    have h1 : a₀ * t * a₀⁻¹ * t⁻¹ ∈ conjSubgroup h (PartTwo.omegaOneSub U) := by
      rw [show a₀ * t * a₀⁻¹ * t⁻¹ = a₀ * (t * a₀⁻¹ * t⁻¹) by group]
      exact Subgroup.mul_mem _ ha₀ (htA₀ _ (Subgroup.inv_mem _ ha₀))
    have h3 := hVC h _ h1 (hcommP a₀ (hSM (hA₀S ha₀)))
    have : a₀ * t * a₀⁻¹ * t⁻¹ ∈ PartTwo.omegaOneSub U ⊓
        conjSubgroup h (PartTwo.omegaOneSub U) := Subgroup.mem_inf.mpr ⟨h3, h1⟩
    rw [hVA, Subgroup.mem_bot] at this
    exact hat' this
  have Pr : NCPair A (conjSubgroup t A) := ⟨hsetup, hAexp, hAA⟩
  have htX : t ∈ Subgroup.normalizer ((A ⊔ conjSubgroup t A : Subgroup G) : Set G) :=
    mem_normalizer_sup_of_swap ht2 A
  obtain ⟨x₀, hx₀, he⟩ := Pr.exists_conj hCen hU
  obtain ⟨x, hx, hxD⟩ := Pr.exists_fixed hCen hU ht2 htX ⟨x₀, hx₀, he⟩
  have hD₀ : PartTwo.omegaOneSub (conjSubgroup x A) =
      conjSubgroup (x * h) (PartTwo.omegaOneSub U) := by
    rw [omegaOneSub_conj hAc, hA₀, conjSubgroup_mul]
  have hNS : PartTwo.omegaOneSub A ⊔ PartTwo.omegaOneSub (conjSubgroup t A) ≤ S := by
    rw [omegaOneSub_conj hAc, hA₀]
    exact sup_le hA₀S hA₀tS
  have hD₀M : PartTwo.omegaOneSub (conjSubgroup x A) ≤ M :=
    le_trans (Pr.omega_conj_le_N hCen hU hx) (le_trans hNS hSM)
  have htD₀ : ∀ d ∈ PartTwo.omegaOneSub (conjSubgroup x A),
      t * d * t⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x A) := by
    intro d hd
    rw [← hxD, omegaOneSub_conj (Tim78.comm_conj hAc x), mem_conjSubgroup,
      show t⁻¹ * (t * d * t⁻¹) * t = d by group]
    exact hd
  have hD₀t : ∀ d ∈ PartTwo.omegaOneSub (conjSubgroup x A), t * d = d * t := by
    intro d hd
    have hw1 : d * t * d⁻¹ * t⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x A) := by
      rw [show d * t * d⁻¹ * t⁻¹ = d * (t * d⁻¹ * t⁻¹) by group]
      exact Subgroup.mul_mem _ hd (htD₀ _ (Subgroup.inv_mem _ hd))
    have hw3 := hVC (x * h) _ (by rw [← hD₀]; exact hw1) (hcommP d (hD₀M hd))
    by_cases hDV : conjSubgroup (x * h) (PartTwo.omegaOneSub U) = PartTwo.omegaOneSub U
    · rw [hD₀, hDV] at hd
      exact htU d (PartTwo.omegaOneSub_le U hd)
    · have hVD := inf_conjSubgroup_eq_bot_of_isTI hVTI hDV
      have : d * t * d⁻¹ * t⁻¹ ∈ PartTwo.omegaOneSub U ⊓
          conjSubgroup (x * h) (PartTwo.omegaOneSub U) :=
        Subgroup.mem_inf.mpr ⟨hw3, by rw [← hD₀]; exact hw1⟩
      rw [hVD, Subgroup.mem_bot] at this
      calc t * d = (d * t * d⁻¹ * t⁻¹)⁻¹ * (d * t) := by group
        _ = d * t := by rw [this, inv_one, one_mul]
  have hcomm_a : ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U),
      a * t * a⁻¹ * t⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x A) := by
    intro a ha
    have haN : a ∈ PartTwo.omegaOneSub A ⊔ PartTwo.omegaOneSub (conjSubgroup t A) :=
      Subgroup.mem_sup_left (by rw [hA₀]; exact ha)
    have h1 := Pr.commutator_mem_omega_of_swap' hCen hU ht2 rfl hx hD₀t haN
    have := (PartTwo.omegaOneSub (conjSubgroup x A)).inv_mem h1
    rwa [show (t * a * t⁻¹ * a⁻¹)⁻¹ = a * t * a⁻¹ * t⁻¹ by group] at this
  have hDV : conjSubgroup (x * h) (PartTwo.omegaOneSub U) = PartTwo.omegaOneSub U := by
    by_contra hne
    have hVD := inf_conjSubgroup_eq_bot_of_isTI hVTI hne
    have h1 := hcomm_a a₀ ha₀
    rw [hD₀] at h1
    have h3 := hVC (x * h) _ h1 (hcommP a₀ (hSM (hA₀S ha₀)))
    have : a₀ * t * a₀⁻¹ * t⁻¹ ∈ PartTwo.omegaOneSub U ⊓
        conjSubgroup (x * h) (PartTwo.omegaOneSub U) := Subgroup.mem_inf.mpr ⟨h3, h1⟩
    rw [hVD, Subgroup.mem_bot] at this
    exact hat' this
  intro a ha
  have := hcomm_a a ha
  rwa [hD₀, hDV] at this

end S3Hyp

end CFSG.RankThree.GF2n.Tim78
