module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.ClassicalGroups.Symplectic.Simple

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem FF81Basis.mem_opp_of_mem_cen_inf (hB : FF81Basis b L B b₁ b₂ b₃) {d : G}
    (hd : d ∈ Cen b ⊓ CenS L) (hco : Nat.Coprime 3 (orderOf d)) : d ∈ Opp 3 (Cen b) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := Cen b ⊓ CenS L with hD
  have h3 : ∀ y ∈ D, IsPGroup 3 (Subgroup.zpowers y) → y ∈ Subgroup.zpowers b := fun y hy hp =>
    hB.mem_zpowers_of_isPGroup hy.1 hy.2 hp
  have hcentral : ∀ y ∈ D, ∀ z ∈ D, IsPGroup 3 (Subgroup.zpowers y) → y * z = z * y := by
    intro y hy z hz hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (h3 y hy hp)
    exact ((Commute.zpow_left
      (Subgroup.mem_centralizer_singleton_iff.mp hz.1).symm k)).eq
  obtain ⟨P⟩ : Nonempty (Sylow 3 D) := inferInstance
  have hpow : ∀ z : D, (∃ k : ℕ, z ^ (3 ^ k) = 1) → IsPGroup 3 (Subgroup.zpowers (z : G)) := by
    rintro z ⟨k, hk⟩
    exact isPGroup_zpowers_of_pow (e := k) (by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one])
  have hPc : Subgroup.normalizer (P : Set D) ≤ Subgroup.centralizer (P : Set D) := by
    intro g _
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hp := hpow h (by
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨h, hh⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩)
    exact Subtype.ext (hcentral h h.2 g g.2 hp)
  set φ := MonoidHom.transferSylow P hPc
  have hcop : Nat.Coprime 3 (Nat.card φ.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow P hPc)
  have hker : ∀ d : D, d ∈ φ.ker ↔ Nat.Coprime 3 (orderOf d) := by
    intro d
    constructor
    · intro hd
      rw [← Subgroup.orderOf_mk (H := φ.ker) d hd]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard _) hcop
    · intro hd
      have hpd : orderOf (φ d) ∣ orderOf d := orderOf_map_dvd φ d
      obtain ⟨k, hk⟩ := P.isPGroup' (φ d)
      have hpk : orderOf (φ d) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
      have hc : Nat.Coprime (orderOf (φ d)) (orderOf d) :=
        (Nat.Coprime.pow_left k hd).coprime_dvd_left hpk
      exact MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp (hc.eq_one_of_dvd hpd))
  set N : Subgroup G := φ.ker.map D.subtype with hN
  have hDn : ∀ g ∈ Cen b, ∀ d ∈ D, g * d * g⁻¹ ∈ D := by
    intro g hg d hd
    refine ⟨?_, ?_⟩
    · exact (Cen b).mul_mem ((Cen b).mul_mem hg hd.1) ((Cen b).inv_mem hg)
    · refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
      have hgN := hB.hyp.hLN hg
      have hx' : g⁻¹ * x * g ∈ L := by
        exact (Subgroup.mem_normalizer_iff.mp hgN (g⁻¹ * x * g)).mpr
          (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx)
      have hc := Subgroup.mem_centralizer_iff.mp hd.2 _ hx'
      calc x * (g * d * g⁻¹) = g * ((g⁻¹ * x * g) * d) * g⁻¹ := by group
        _ = g * (d * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
        _ = g * d * g⁻¹ * x := by group
  have hNnorm : (N.subgroupOf (Cen b)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨d, hd, hdn⟩ := hn
    have hgd := hDn g g.2 (n : G) (hdn ▸ d.2)
    refine ⟨⟨_, hgd⟩, (hker _).mpr ?_, by simp⟩
    rw [Subgroup.orderOf_mk, show (g : G) * n * (g : G)⁻¹ = MulAut.conj (g : G) n from rfl,
      MulEquiv.orderOf_eq, ← hdn]
    have := (hker d).mp hd
    rwa [← Subgroup.orderOf_coe] at this⟩
  have hle : N ≤ Cen b := (Subgroup.map_subtype_le _).trans inf_le_left
  have hNco : Nat.Coprime 3 (Nat.card (N.subgroupOf (Cen b))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective D.subtype_injective]
    exact hcop
  have hNle : N.subgroupOf (Cen b) ≤ CFSG.pPrimeCore 3 ↥(Cen b) := le_sSup ⟨hNnorm, hNco⟩
  have hdN : (⟨d, hd.1⟩ : Cen b) ∈ N.subgroupOf (Cen b) :=
    Subgroup.mem_subgroupOf.mpr ⟨⟨d, hd⟩, (hker _).mpr (by rwa [Subgroup.orderOf_mk]), rfl⟩
  exact ⟨⟨d, hd.1⟩, hNle hdN, rfl⟩

theorem FF81Basis.opp_comm (hB : FF81Basis b L B b₁ b₂ b₃) {o l : G}
    (ho : o ∈ Opp 3 (Cen b)) (hl : l ∈ L) : o * l = l * o := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hON := CFSG.pPrimeCore_normal (p := 3) (G := ↥(Cen b))
  have hOco : Nat.Coprime 3 (Nat.card (Opp 3 (Cen b))) := by
    rw [Opp, CFSG.inSubgroup, Subgroup.card_map_of_injective (Cen b).subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hOL : Opp 3 (Cen b) ⊓ L = ⊥ := by
    haveI : IsSimpleGroup L :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1
        hB.hyp.model
    haveI : ((Opp 3 (Cen b) ⊓ L).subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact ⟨inSubgroup_conj_mem hON (hB.hyp.hLC g.2) hn.1,
        L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Opp 3 (Cen b) ⊓ L).subgroupOf L) with h | h
    · refine eq_bot_iff.mpr fun x hx => ?_
      have : (⟨x, hx.2⟩ : L) ∈ (Opp 3 (Cen b) ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · exfalso
      have hLO : L ≤ Opp 3 (Cen b) := fun x hx => by
        have : (⟨x, hx⟩ : L) ∈ (Opp 3 (Cen b) ⊓ L).subgroupOf L := by
          rw [h]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).1
      have h1 := Subgroup.card_dvd_of_le hLO
      rw [hB.card_L] at h1
      exact absurd (hOco.coprime_dvd_right h1) (by norm_num)
  have hoC : o ∈ Cen b := Subgroup.map_subtype_le _ ho
  have h1 : o * l * o⁻¹ * l⁻¹ ∈ Opp 3 (Cen b) ⊓ L := by
    refine ⟨?_, ?_⟩
    · rw [show o * l * o⁻¹ * l⁻¹ = o * (l * o⁻¹ * l⁻¹) by group]
      exact Subgroup.mul_mem _ ho (inSubgroup_conj_mem hON (hB.hyp.hLC hl) (Subgroup.inv_mem _ ho))
    · exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hB.hyp.hLN hoC) l).mp hl) (L.inv_mem hl)
  rw [hOL, Subgroup.mem_bot] at h1
  calc o * l = o * l * o⁻¹ * l⁻¹ * (l * o) := by group
    _ = l * o := by rw [h1, one_mul]

theorem mem_normalizer_sup_inf {R T L : Subgroup G} {g : G} (hR : g ∈ Nor R) (hT : g ∈ Nor T)
    (hL : g ∈ Nor L) : g ∈ Nor ((R ⊔ T) ⊓ L) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hR hT hL ⊢
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, Subgroup.map_sup, hR, hT, hL]

theorem ff81_4_4 :
    KF_Sp6TorusFree → ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G)
      (b₁ b₂ b₃ t₀ : G), FF81Sec4 b L B b₁ b₂ b₃ t₀ → FF81Conc4_3 L t₀ → Opp 3 (Cen b) = ⊥ := by
  intro hKF G _ _ b L B b₁ b₂ b₃ t₀ h4 h43
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB := h4.basis
  set O := Opp 3 (Cen b) with hOdef
  set T := Op 2 (Cen t₀) with hT
  set B₁ := Subgroup.closure ({b₁, b₂, b₃} : Set G) with hB₁
  have hON := CFSG.pPrimeCore_normal (p := 3) (G := ↥(Cen b))
  have hLt : L ≤ Cen t₀ := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h4.ht₀L x hx)
  have hTn : ∀ g ∈ Cen t₀, ∀ s ∈ T, g * s * g⁻¹ ∈ T := fun g hg s hs =>
    inSubgroup_conj_mem (CFSG.pCore_normal (p := 2) (G := ↥(Cen t₀))) hg hs
  have hTcard : Nat.card T = 2 ^ 7 := h43.2.1.2
  have hB₁L : B₁ ≤ L := (Subgroup.closure_le _).mpr (by
    intro z hz; rcases hz with rfl | rfl | rfl; exacts [hB.hb₁, hB.hb₂, hB.hb₃])
  have hstep1 : ∀ R : Subgroup G, R ≤ Cen t₀ → B₁ ≤ Nor R → Nat.Coprime 3 (Nat.card R) →
      R ≤ T := by
    intro R hRC hRN hRco
    have hRT : R ≤ Subgroup.normalizer (T : Set G) := fun r hr =>
      Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => hTn r (hRC hr) s hs, fun hs => by
        have := hTn r⁻¹ ((Cen t₀).inv_mem (hRC hr)) _ hs
        rwa [show r⁻¹ * (r * s * r⁻¹) * r⁻¹⁻¹ = s by group] at this⟩
    have e := card_sup_mul_card_inf R T hRT
    have hsupco : Nat.Coprime 3 (Nat.card ↥(R ⊔ T)) := by
      refine Nat.Coprime.coprime_dvd_right (Dvd.intro _ e) (Nat.Coprime.mul_right hRco ?_)
      rw [hTcard]; norm_num
    have hR' := hKF G L hB.hyp.model B₁ hB₁L hB.elem ((R ⊔ T) ⊓ L) inf_le_right (by
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      have hxL : x ∈ L := hB₁L (Subgroup.subset_closure hx)
      refine mem_normalizer_sup_inf (hRN (Subgroup.subset_closure hx)) ?_ ?_
      · exact Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => hTn x (hLt hxL) s hs,
          fun hs => by
            have := hTn x⁻¹ ((Cen t₀).inv_mem (hLt hxL)) _ hs
            rwa [show x⁻¹ * (x * s * x⁻¹) * x⁻¹⁻¹ = s by group] at this⟩
      · exact Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs =>
          L.mul_mem (L.mul_mem hxL hs) (L.inv_mem hxL), fun hs => by
            have := L.mul_mem (L.mul_mem (L.inv_mem hxL) hs) hxL
            rwa [show x⁻¹ * (x * s * x⁻¹) * x = s by group] at this⟩)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hsupco)
    intro r hr
    have hr' : r ∈ setMul T L := by rw [h43.1]; exact hRC hr
    obtain ⟨s, hs, l, hl, rfl⟩ := hr'
    have hl1 : l ∈ (R ⊔ T) ⊓ L := by
      refine ⟨?_, hl⟩
      have : s⁻¹ * (s * l) ∈ R ⊔ T :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right (T.inv_mem hs)) (Subgroup.mem_sup_left hr)
      rwa [show s⁻¹ * (s * l) = l by group] at this
    rw [hR', Subgroup.mem_bot] at hl1
    rw [hl1, mul_one]; exact hs
  obtain ⟨σ, -, hσb, hσb₁, hσb₂, hσb₃⟩ := h4.caseI.1.1.2.2.2.1
  have ht₀b₁ : t₀ * b₁ = b₁ * t₀ := (Subgroup.mem_centralizer_iff.mp h4.ht₀L b₁ hB.hb₁).symm
  have ht₁b : σ * t₀ * σ⁻¹ ∈ Cen b := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hσb₁]
    exact conj_commute ht₀b₁
  have ht₀2 : t₀ * t₀ = 1 := by
    have := pow_orderOf_eq_one t₀
    rwa [h4.ht₀, sq] at this
  have ht₁L : σ * t₀ * σ⁻¹ ∈ L := by
    obtain ⟨l, hlL, hl⟩ := kf_sp62Out G L hB.hyp.model _ (hB.hyp.hLN ht₁b)
    set t₁ := σ * t₀ * σ⁻¹ with ht₁
    have hdL : l⁻¹ * t₁ ∈ CenS L := Subgroup.mem_centralizer_iff.mpr fun y hy => by
      have := hl y hy
      calc y * (l⁻¹ * t₁) = l⁻¹ * (l * y * l⁻¹) * t₁ := by group
        _ = l⁻¹ * (t₁ * y * t₁⁻¹) * t₁ := by rw [this]
        _ = l⁻¹ * t₁ * y := by group
    have hdb : l⁻¹ * t₁ ∈ Cen b := (Cen b).mul_mem ((Cen b).inv_mem (hB.hyp.hLC hlL)) ht₁b
    have hdl : (l⁻¹ * t₁) * l = l * (l⁻¹ * t₁) := (Subgroup.mem_centralizer_iff.mp hdL l hlL).symm
    have ht₁2 : t₁ * t₁ = 1 := by
      rw [ht₁, show σ * t₀ * σ⁻¹ * (σ * t₀ * σ⁻¹) = σ * (t₀ * t₀) * σ⁻¹ by group, ht₀2]; group
    have hd2 : (l⁻¹ * t₁) * (l⁻¹ * t₁) = 1 := by
      have hl2 : l * l * ((l⁻¹ * t₁) * (l⁻¹ * t₁)) = 1 := by
        calc l * l * ((l⁻¹ * t₁) * (l⁻¹ * t₁)) = l * ((l * (l⁻¹ * t₁)) * (l⁻¹ * t₁)) := by group
          _ = l * (((l⁻¹ * t₁) * l) * (l⁻¹ * t₁)) := by rw [hdl]
          _ = t₁ * t₁ := by group
          _ = 1 := ht₁2
      have hmem : l * l ∈ L ⊓ CenS L := by
        refine ⟨L.mul_mem hlL hlL, ?_⟩
        rw [eq_inv_of_mul_eq_one_left hl2]
        exact (CenS L).inv_mem ((CenS L).mul_mem hdL hdL)
      rw [hB.inf_cenS_self, Subgroup.mem_bot] at hmem
      rwa [hmem, one_mul] at hl2
    have hdco : Nat.Coprime 3 (orderOf (l⁻¹ * t₁)) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hd2))
        (by norm_num)
    have hdO := hB.mem_opp_of_mem_cen_inf ⟨hdb, hdL⟩ hdco
    have hd1 : l⁻¹ * t₁ = 1 := by
      have h2 : orderOf (l⁻¹ * t₁) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hd2)
      have hO : orderOf (l⁻¹ * t₁) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard _ hdO
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact orderOf_eq_one_iff.mp h
      · rw [h] at hO
        exact absurd (even_iff_two_dvd.mpr hO) (Nat.not_even_iff_odd.mpr hB.o3odd)
    have : t₁ = l := by
      calc t₁ = l * (l⁻¹ * t₁) := by group
        _ = l := by rw [hd1, mul_one]
    rw [this]; exact hlL
  have hR'C : conjBy σ⁻¹ O ≤ Cen t₀ := by
    rintro _ ⟨o, ho, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := conj_commute (a := σ⁻¹) (hB.opp_comm ho ht₁L)
    rw [show σ⁻¹ * (σ * t₀ * σ⁻¹) * σ⁻¹⁻¹ = t₀ by group] at h
    exact h
  have hR'N : B₁ ≤ Nor (conjBy σ⁻¹ O) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    have hσx : σ * x * σ⁻¹ ∈ Cen b := by
      rcases hx with rfl | rfl | rfl
      · rw [hσb₁]; exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · rw [hσb₂]; exact hB.hyp.hLC hB.hb₂
      · rw [hσb₃]; exact hB.hyp.hLC hB.hb₃
    refine Subgroup.mem_normalizer_fintype fun w hw => ?_
    obtain ⟨o, ho, rfl⟩ := hw
    refine ⟨(σ * x * σ⁻¹) * o * (σ * x * σ⁻¹)⁻¹, inSubgroup_conj_mem hON hσx ho, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hOco : Nat.Coprime 3 (Nat.card O) := by
    rw [hOdef, Opp, CFSG.inSubgroup, Subgroup.card_map_of_injective (Cen b).subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hcardR' : Nat.card (conjBy σ⁻¹ O) = Nat.card O :=
    Subgroup.card_map_of_injective (MulAut.conj σ⁻¹).injective
  have hle := hstep1 _ hR'C hR'N (by rw [hcardR']; exact hOco)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcardR', hTcard] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hodd := hB.o3odd
  rw [← hOdef, hk] at hodd
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exact absurd hodd (by rw [Nat.not_odd_iff_even]; exact (Nat.even_pow' h.ne').mpr even_two)
  rw [hk0, pow_zero] at hk
  exact Subgroup.card_eq_one.mp hk

end CFSG.RankThree.PartTwo.Sec21.FF81
