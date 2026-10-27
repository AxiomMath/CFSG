module

public import CFSG.RankThree.GF2n.Tim78S33Step

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_odd_conj {x y d : G} {m n : ℕ} (hm : Odd m) (hy : y ^ m = 1)
    (hyx : y * x * y⁻¹ = x * d) (hyd : y * d = d * y) (hd : d ^ 2 ^ n = 1) : d = 1 := by
  have hk : ∀ k : ℕ, y ^ k * x * (y ^ k)⁻¹ = x * d ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hdk : y * d ^ k * y⁻¹ = d ^ k := by
          rw [(Commute.pow_right hyd k).eq]
          group
        calc y ^ (k + 1) * x * (y ^ (k + 1))⁻¹ = y * (y ^ k * x * (y ^ k)⁻¹) * y⁻¹ := by group
          _ = y * (x * d ^ k) * y⁻¹ := by rw [ih]
          _ = (y * x * y⁻¹) * (y * d ^ k * y⁻¹) := by group
          _ = x * d ^ (k + 1) := by rw [hyx, hdk, pow_succ', mul_assoc]
  have h1 := hk m
  rw [hy, one_mul, inv_one, mul_one] at h1
  have hdm : d ^ m = 1 := by
    have := congrArg (x⁻¹ * ·) h1
    simpa using this.symm
  have hcop : Nat.Coprime m (2 ^ n) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  have h2 := orderOf_dvd_of_pow_eq_one hdm
  have h3 := orderOf_dvd_of_pow_eq_one hd
  have h4 : orderOf d = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h3
  exact orderOf_eq_one_iff.mp h4

namespace S3Hyp

variable {M U : Subgroup G} (H : S3Hyp M U)
include H

theorem le_Q_of_le (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaComm (PartTwo.omegaOneSub U)) {h : G}
    (hhM : conjSubgroup h (PartTwo.omegaOneSub U) ≤ M) :
    conjSubgroup h (PartTwo.omegaOneSub U) ≤ inSubgroup (pCore 2) M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hQ2, hQM, hMQ⟩ := inSubgroup_pCore_two M
  have hUQ : U ≤ inSubgroup (pCore 2) M := le_inSubgroup_pCore H.le H.normal H.two
  have hVQ : PartTwo.omegaOneSub U ≤ inSubgroup (pCore 2) M :=
    le_trans (PartTwo.omegaOneSub_le U) hUQ
  by_cases hV : conjSubgroup h (PartTwo.omegaOneSub U) = PartTwo.omegaOneSub U
  · rw [hV]
    exact hVQ
  have hroot := H.root hCen hU
  have hVe : ∀ v ∈ PartTwo.omegaOneSub U, v * v = 1 := fun v hv =>
    ((mem_omegaOneSub_iff H.comm).mp hv).2
  have hA₀2 : IsPGroup 2 (conjSubgroup h (PartTwo.omegaOneSub U)) :=
    (H.two.to_le (PartTwo.omegaOneSub_le U)).map (MulAut.conj h).toMonoidHom
  obtain ⟨P₀, hP₀⟩ := (hA₀2.comap_of_injective M.subtype
    M.subtype_injective).exists_le_sylow
  set S := (P₀ : Subgroup ↥M).map M.subtype with hSdef
  have hSM : S ≤ M := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := P₀.isPGroup'.map M.subtype
  have hA₀S : conjSubgroup h (PartTwo.omegaOneSub U) ≤ S := fun z hz =>
    ⟨⟨z, hhM hz⟩, hP₀ hz, rfl⟩
  have hQS : inSubgroup (pCore 2) M ≤ S := by
    have hn : ((inSubgroup (pCore 2) M).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMQ
    have hp : IsPGroup 2 ((inSubgroup (pCore 2) M).subgroupOf M) :=
      hQ2.comap_of_injective _ Subtype.val_injective
    have hle := IsPGroup.le_sylow_of_normal hp P₀
    intro z hz
    exact ⟨⟨z, hQM hz⟩, hle (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  set P := inSubgroup (pCore 2) M ⊓ Subgroup.centralizer (U : Set G) with hPdef
  have hPQ : P ≤ inSubgroup (pCore 2) M := inf_le_left
  have hP2 : IsPGroup 2 P := hQ2.to_le hPQ
  have hMP : M ≤ Subgroup.normalizer (P : Set G) := fun m hm =>
    mem_normalizer_inf (hMQ hm) (mem_normalizer_centralizer (H.normal hm))
  have hPV : ∀ p ∈ P, ∀ v ∈ PartTwo.omegaOneSub U, p * v = v * p := fun p hp v hv =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hp).2 v
      (PartTwo.omegaOneSub_le U hv)).symm
  have hVP : PartTwo.omegaOneSub U ≤ P := fun v hv =>
    Subgroup.mem_inf.mpr ⟨hVQ hv, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      H.comm u hu v (PartTwo.omegaOneSub_le U hv)⟩
  set P₁ := Subgroup.closure {t | t ∈ P ∧ t * t = 1} with hP₁def
  have hP₁P : P₁ ≤ P := (Subgroup.closure_le _).mpr fun t ht => ht.1
  have hconjP₁ : ∀ m ∈ M, ∀ x ∈ P₁, m * x * m⁻¹ ∈ P₁ := by
    intro m hm x hx
    induction hx using Subgroup.closure_induction with
    | mem t ht =>
        refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp (hMP hm) t).mp ht.1, ?_⟩
        calc m * t * m⁻¹ * (m * t * m⁻¹) = m * (t * t) * m⁻¹ := by group
          _ = 1 := by rw [ht.2]; group
    | one => simp
    | mul x y hx hy ihx ihy =>
        rw [show m * (x * y) * m⁻¹ = (m * x * m⁻¹) * (m * y * m⁻¹) by group]
        exact P₁.mul_mem ihx ihy
    | inv x hx ihx =>
        rw [show m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ by group]
        exact P₁.inv_mem ihx
  have hconjV : ∀ m ∈ M, ∀ v ∈ PartTwo.omegaOneSub U, m * v * m⁻¹ ∈ PartTwo.omegaOneSub U :=
    fun m hm v hv => (Subgroup.mem_normalizer_iff.mp (H.le_normalizer_omega hm) v).mp hv
  have hA₀V : ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U), ∀ v ∈ PartTwo.omegaOneSub U,
      a * v = v * a := by
    have hc := commute_of_isRootTypeTI hroot (g := h) (h := 1) (fun hbot => by
      have hA₀ne : conjSubgroup h (PartTwo.omegaOneSub U) ≠ ⊥ := by
        intro hb
        apply H.omega_ne_bot
        have := card_conjSubgroup h (PartTwo.omegaOneSub U)
        rw [hb, Subgroup.card_bot] at this
        exact Subgroup.eq_bot_of_card_eq _ this.symm
      apply hA₀ne
      rw [eq_bot_iff, ← hbot]
      intro a ha
      refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
      rw [conjSubgroup_one]
      exact H.le_normalizer_omega (hhM ha))
    intro a ha v hv
    exact hc a ha v (by rw [conjSubgroup_one]; exact hv)
  have hC3 : ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U), ∀ x ∈ P₁,
      a * x * a⁻¹ * x⁻¹ ∈ PartTwo.omegaOneSub U := by
    intro a ha x hx
    induction hx using Subgroup.closure_induction with
    | mem t ht => exact H.comm_mem_of_invol hCen hU hS hS2 hSM hQS hA₀S hV ht.1 ht.2 a ha
    | one => simp
    | mul x y hx hy ihx ihy =>
        have hxy : x * (a * y * a⁻¹ * y⁻¹) * x⁻¹ = a * y * a⁻¹ * y⁻¹ := by
          rw [hPV x (hP₁P hx) _ ihy]
          group
        rw [show a * (x * y) * a⁻¹ * (x * y)⁻¹ =
          (a * x * a⁻¹ * x⁻¹) * (x * (a * y * a⁻¹ * y⁻¹) * x⁻¹) by group, hxy]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ihx =>
        have hxx : x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x = (a * x * a⁻¹ * x⁻¹)⁻¹ := by
          have h1 := hPV x (hP₁P hx) _ (Subgroup.inv_mem _ ihx)
          calc x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x =
              x⁻¹ * ((a * x * a⁻¹ * x⁻¹)⁻¹ * x) := by group
            _ = x⁻¹ * (x * (a * x * a⁻¹ * x⁻¹)⁻¹) := by rw [h1]
            _ = (a * x * a⁻¹ * x⁻¹)⁻¹ := by group
        rw [show a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x by group, hxx]
        exact Subgroup.inv_mem _ ihx
  have hC4 : ∀ a ∈ conjSubgroup h (PartTwo.omegaOneSub U), ∀ p ∈ P,
      a * p * a⁻¹ * p⁻¹ ∈ P₁ := by
    intro a ha p hp
    apply Subgroup.subset_closure
    have haM := hhM ha
    refine ⟨Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hMP haM) p).mp hp)
      (Subgroup.inv_mem _ hp), ?_⟩
    have hpS : p ∈ S := hQS (hPQ hp)
    have hb : p * a * p⁻¹ ∈ conjSubgroup (p * h) (PartTwo.omegaOneSub U) := by
      rw [conjSubgroup_mul, mem_conjSubgroup, show p⁻¹ * (p * a * p⁻¹) * p = a by group]
      exact ha
    have hbS : conjSubgroup (p * h) (PartTwo.omegaOneSub U) ≤ S := by
      intro z hz
      rw [conjSubgroup_mul, mem_conjSubgroup] at hz
      rw [show z = p * (p⁻¹ * z * p) * p⁻¹ by group]
      exact S.mul_mem (S.mul_mem hpS (hA₀S hz)) (S.inv_mem hpS)
    have hab := hS S hS2 h (p * h) hA₀S hbS a ha _ hb
    have haa := mul_self_of_mem_conj hVe ha
    have hbb := mul_self_of_mem_conj hVe hb
    have hbi : (p * a * p⁻¹)⁻¹ = p * a * p⁻¹ := inv_eq_of_mul_eq_one_right hbb
    rw [show a * p * a⁻¹ * p⁻¹ = a * (p * a * p⁻¹)⁻¹ by group, hbi]
    calc a * (p * a * p⁻¹) * (a * (p * a * p⁻¹)) = a * ((p * a * p⁻¹) * a) * (p * a * p⁻¹) := by
          group
      _ = a * (a * (p * a * p⁻¹)) * (p * a * p⁻¹) := by rw [← hab]
      _ = (a * a) * ((p * a * p⁻¹) * (p * a * p⁻¹)) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  let K : Subgroup G :=
    { carrier := {x | x ∈ M ∧ (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ P₁) ∧
        (∀ p ∈ P₁, x * p * x⁻¹ * p⁻¹ ∈ PartTwo.omegaOneSub U) ∧
        ∀ v ∈ PartTwo.omegaOneSub U, x * v = v * x}
      one_mem' := ⟨M.one_mem, fun p _ => by simp, fun p _ => by simp, fun v _ => by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨M.mul_mem hx.1 hy.1, fun p hp => by
          rw [show x * y * p * (x * y)⁻¹ * p⁻¹ =
            (x * (y * p * y⁻¹ * p⁻¹) * x⁻¹) * (x * p * x⁻¹ * p⁻¹) by group]
          exact P₁.mul_mem (hconjP₁ x hx.1 _ (hy.2.1 p hp)) (hx.2.1 p hp), fun p hp => by
          rw [show x * y * p * (x * y)⁻¹ * p⁻¹ =
            (x * (y * p * y⁻¹ * p⁻¹) * x⁻¹) * (x * p * x⁻¹ * p⁻¹) by group]
          exact Subgroup.mul_mem _ (hconjV x hx.1 _ (hy.2.2.1 p hp)) (hx.2.2.1 p hp),
          fun v hv => by
          calc x * y * v = x * (y * v) := by group
            _ = x * (v * y) := by rw [hy.2.2.2 v hv]
            _ = (x * v) * y := by group
            _ = (v * x) * y := by rw [hx.2.2.2 v hv]
            _ = v * (x * y) := by group⟩
      inv_mem' := fun {x} hx => ⟨M.inv_mem hx.1, fun p hp => by
          rw [show x⁻¹ * p * x⁻¹⁻¹ * p⁻¹ = x⁻¹ * (x * p * x⁻¹ * p⁻¹)⁻¹ * x⁻¹⁻¹ by group]
          exact hconjP₁ _ (M.inv_mem hx.1) _ (P₁.inv_mem (hx.2.1 p hp)), fun p hp => by
          rw [show x⁻¹ * p * x⁻¹⁻¹ * p⁻¹ = x⁻¹ * (x * p * x⁻¹ * p⁻¹)⁻¹ * x⁻¹⁻¹ by group]
          exact hconjV _ (M.inv_mem hx.1) _ (Subgroup.inv_mem _ (hx.2.2.1 p hp)),
          fun v hv => by
          have h1 := hx.2.2.2 v hv
          calc x⁻¹ * v = x⁻¹ * (v * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * v) * x⁻¹ := by rw [h1]
            _ = v * x⁻¹ := by group⟩ }
  have hA₀K : ∀ m : ↥M, conjSubgroup (m : G) (conjSubgroup h (PartTwo.omegaOneSub U)) ≤ K := by
    intro m z hz
    rw [mem_conjSubgroup] at hz
    set a := (m : G)⁻¹ * z * m with ha_def
    have hz' : z = (m : G) * a * (m : G)⁻¹ := by rw [ha_def]; group
    have hmi : (m : G)⁻¹ ∈ M := M.inv_mem m.2
    refine ⟨?_, fun p hp => ?_, fun p hp => ?_, fun v hv => ?_⟩
    · rw [hz']
      exact M.mul_mem (M.mul_mem m.2 (hhM hz)) hmi
    · have hp' : (m : G)⁻¹ * p * (m : G)⁻¹⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hMP hmi) p).mp hp
      have h1 := hconjP₁ _ m.2 _ (hC4 a hz _ hp')
      rwa [show (m : G) * (a * ((m : G)⁻¹ * p * (m : G)⁻¹⁻¹) * a⁻¹ *
        ((m : G)⁻¹ * p * (m : G)⁻¹⁻¹)⁻¹) * (m : G)⁻¹ = z * p * z⁻¹ * p⁻¹ by rw [hz']; group]
        at h1
    · have hp' : (m : G)⁻¹ * p * (m : G)⁻¹⁻¹ ∈ P₁ := hconjP₁ _ hmi _ hp
      have h1 := hconjV _ m.2 _ (hC3 a hz _ hp')
      rwa [show (m : G) * (a * ((m : G)⁻¹ * p * (m : G)⁻¹⁻¹) * a⁻¹ *
        ((m : G)⁻¹ * p * (m : G)⁻¹⁻¹)⁻¹) * (m : G)⁻¹ = z * p * z⁻¹ * p⁻¹ by rw [hz']; group]
        at h1
    · have hv' : (m : G)⁻¹ * v * (m : G)⁻¹⁻¹ ∈ PartTwo.omegaOneSub U := hconjV _ hmi _ hv
      have h1 := hA₀V a hz _ hv'
      rw [hz']
      calc (m : G) * a * (m : G)⁻¹ * v =
          (m : G) * (a * ((m : G)⁻¹ * v * (m : G)⁻¹⁻¹)) * (m : G)⁻¹ := by group
        _ = (m : G) * (((m : G)⁻¹ * v * (m : G)⁻¹⁻¹) * a) * (m : G)⁻¹ := by rw [h1]
        _ = v * ((m : G) * a * (m : G)⁻¹) := by group
  set L := ⨆ m : ↥M, conjSubgroup (m : G) (conjSubgroup h (PartTwo.omegaOneSub U)) with hLdef
  have hLK : L ≤ K := iSup_le hA₀K
  have hLM : L ≤ M := fun z hz => (hLK hz).1
  have hML : M ≤ Subgroup.normalizer (L : Set G) := le_normalizer_iSup
  have hodd : ∀ y ∈ K, Odd (orderOf y) → ∀ p ∈ P, y * p = p * y := by
    intro y hy hyo
    have hy1 : y ^ orderOf y = 1 := pow_orderOf_eq_one y
    have hstep1 : ∀ x ∈ P₁, y * x = x * y := by
      intro x hx
      have hc := hy.2.2.1 x hx
      have hd : x⁻¹ * (y * x * y⁻¹) = y * x * y⁻¹ * x⁻¹ := by
        have h1 := hPV x (hP₁P hx) _ hc
        calc x⁻¹ * (y * x * y⁻¹) = x⁻¹ * ((y * x * y⁻¹ * x⁻¹) * x) := by group
          _ = x⁻¹ * (x * (y * x * y⁻¹ * x⁻¹)) := by rw [h1]
          _ = y * x * y⁻¹ * x⁻¹ := by group
      have hd1 := eq_one_of_odd_conj (n := 1) hyo hy1
        (show y * x * y⁻¹ = x * (x⁻¹ * (y * x * y⁻¹)) by group)
        (by rw [hd]; exact hy.2.2.2 _ hc)
        (by rw [hd, pow_one, sq]; exact hVe _ hc)
      calc y * x = (y * x * y⁻¹) * y := by group
        _ = x * (x⁻¹ * (y * x * y⁻¹)) * y := by group
        _ = x * y := by rw [hd1, mul_one]
    intro p hp
    have hc := hy.2.1 p hp
    have hdP₁ : p⁻¹ * (y * p * y⁻¹) ∈ P₁ := by
      have := hconjP₁ _ (hPQ.trans hQM (P.inv_mem hp)) _ hc
      rwa [show p⁻¹ * (y * p * y⁻¹ * p⁻¹) * p⁻¹⁻¹ = p⁻¹ * (y * p * y⁻¹) by group] at this
    obtain ⟨n, hn⟩ := hP2 ⟨_, hP₁P hdP₁⟩
    have hd1 := eq_one_of_odd_conj (n := n) hyo hy1
      (show y * p * y⁻¹ = p * (p⁻¹ * (y * p * y⁻¹)) by group) (hstep1 _ hdP₁)
      (by simpa using congrArg Subtype.val hn)
    calc y * p = (y * p * y⁻¹) * y := by group
      _ = p * (p⁻¹ * (y * p * y⁻¹)) * y := by group
      _ = p * y := by rw [hd1, mul_one]
  have hα := tim78_2_9_alpha H.fstar H.le H.normal
    ⟨⟨fun a b => Subtype.ext (H.comm _ a.2 _ b.2)⟩⟩ hPdef
  have hL2 : IsPGroup 2 L := by
    intro z
    obtain ⟨a, ha, -⟩ := exists_odd_orderOf_pow (z : G)
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    have hyL : (z : G) ^ 2 ^ a ∈ L := L.pow_mem z.2 _
    have hyK := hLK hyL
    have hyC : (z : G) ^ 2 ^ a ∈ M ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨hyK.1, Subgroup.mem_centralizer_iff.mpr fun p hp => (hodd _ hyK ha p hp).symm⟩
    rw [hα] at hyC
    exact eq_one_of_odd_of_isPGroup hP2 hyC.1 ha
  have hLQ : L ≤ inSubgroup (pCore 2) M := le_inSubgroup_pCore hLM hML hL2
  intro z hz
  refine hLQ (Subgroup.mem_iSup_of_mem ⟨1, M.one_mem⟩ ?_)
  rw [conjSubgroup_one]
  exact hz

theorem weaklyClosed_omega (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (hS : SigmaComm (PartTwo.omegaOneSub U)) :
    ∀ g : G, conjSubgroup g (PartTwo.omegaOneSub U) ≤ M →
      conjSubgroup g (PartTwo.omegaOneSub U) = PartTwo.omegaOneSub U := by
  intro g hg
  obtain ⟨hQ2, -, -⟩ := inSubgroup_pCore_two M
  have hgQ := H.le_Q_of_le hCen hU hS hg
  have hVQ : conjSubgroup 1 (PartTwo.omegaOneSub U) ≤ inSubgroup (pCore 2) M := by
    rw [conjSubgroup_one]
    exact le_trans (PartTwo.omegaOneSub_le U) (le_inSubgroup_pCore H.le H.normal H.two)
  have hmem := H.mem_of_comm (g := g)
    (fun k hk => hS _ hQ2 k g (H.le_Q_of_le hCen hU hS hk) hgQ)
    (fun k hk a ha c hc => hS _ hQ2 k 1 (H.le_Q_of_le hCen hU hS hk) hVQ a ha c
      (by rw [conjSubgroup_one]; exact hc))
  exact conjSubgroup_eq_self_iff.mpr (H.le_normalizer_omega hmem)

theorem false_of_sigmaComm (hGold : GoldschmidtInput) (hCen : BenderCenterInput)
    (hU : UnitaryTwoGenerationInput) (o2 : pCore 2 G = ⊥)
    (hS : SigmaComm (PartTwo.omegaOneSub U)) : False :=
  H.not_weaklyClosed hGold hCen hU o2 (H.weaklyClosed_omega hCen hU hS)

end S3Hyp

end CFSG.RankThree.GF2n.Tim78
