module

public import CFSG.RankThree.PartOne.U5E.CenterOdd
public import CFSG.RankThree.PartOne.K159.CompGenFive
public import CFSG.RankThree.PartOne.K159.ThetaChain
public import CFSG.RankThree.PartOne.S12.Sec153Weyl
public import CFSG.RankThree.PartOne.S12.Sec1510FiveDefs
public import CFSG.RankThree.PartOne.S15K.LayerData
import CFSG.RankThree.PartOne.N143.CaseB1Theta
import CFSG.RankThree.PartOne.S13K.ThetaFixed
import CFSG.RankThree.PartOne.S10.PlaneTwoGroupLemmas
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSetting
public import CFSG.RankThree.PartOne.S12.Sec159Defs
public import CFSG.RankThree.PartOne.TCB.Schreier
import CFSG.RankThree.PartOne.N143.QEqual
import CFSG.RankThree.PartOne.S10.PlaneContract
import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional

public section

namespace CFSG.RankThree.PartOne.U5E

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.U5K
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem kZero_inf_thetaCore_eq_bot (hp : p.Prime) {E : Subgroup G} {t : MulAut E} {e : G}
    (hq : CFSG.IsQuasisimple ↥(kZero p E t)) (hKc : Subgroup.center ↥(kZero p E t) = ⊥)
    (hKe : kZero p E t ≤ Subgroup.centralizer ({e} : Set G)) :
    kZero p E t ⊓ thetaCore p e = ⊥ := by
  classical
  set K := kZero p E t with hK
  have hKN : K ≤ Subgroup.normalizer (thetaCore p e : Set G) :=
    le_normalizer_theta_of_le_normalizer hp (hKe.trans Subgroup.le_normalizer)
  have hle : K ⊓ thetaCore p e ≤ K := inf_le_left
  have hMn : ((K ⊓ thetaCore p e).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hkθ := Subgroup.mem_normalizer_iff.1 (hKN hk) x
    constructor
    · rintro ⟨hxK, hxθ⟩
      exact ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), hkθ.1 hxθ⟩
    · rintro ⟨hxK, hxθ⟩
      refine ⟨?_, hkθ.2 hxθ⟩
      have := K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
      simpa [mul_assoc] using this
  have hθs : Group.IsSolvable ↥(thetaCore p e) := (theta_solvable_and_not_dvd hp _).1
  have hMs : Group.IsSolvable ↥((K ⊓ thetaCore p e).subgroupOf K) := by
    have h1 : Group.IsSolvable ↥(K ⊓ thetaCore p e) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_right :
        K ⊓ thetaCore p e ≤ thetaCore p e))
        (Subgroup.inclusion_injective (inf_le_right : K ⊓ thetaCore p e ≤ thetaCore p e))
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).injective
  have hz := N143.normal_solvable_le_center hq hMn hMs
  rw [hKc] at hz
  refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
  have : (⟨x, hx.1⟩ : ↥K) ∈ (K ⊓ thetaCore p e).subgroupOf K := hx
  have h2 := hz this
  rw [Subgroup.mem_bot] at h2
  exact congrArg Subtype.val h2

theorem autFixedInG_mem_admissible (h15 : Sec15Hyp G p A c L E) (hcardE : Nat.card ↥E = p ^ 4)
    {f : ℕ} {t : MulAut E} (ht : t ∈ reflectionSet p E) (hAtt : KFAt p E f t) :
    autFixedInG E t ∈ admissibleTriples p E := by
  classical
  obtain ⟨hne, hmod, hcent, hmov, -⟩ := hAtt
  obtain ⟨s, hs1, hs2⟩ := exists_involution_of_model_psl_two hmod
  have hsK : (s : G) ∈ kZero p E t := s.2
  have hs1' : (s : G) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hs2' : (s : G) ^ 2 = 1 := by
    have := congrArg Subtype.val hs2
    simpa using this
  have hord : orderOf (s : G) = 2 := orderOf_eq_prime hs2' hs1'
  have hEel : IsElementaryAbelian p ↥E := h15.h12.E_elem
  have hle : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  refine ⟨hle, Sec1514Five.isElementaryAbelian_of_le_aux hEel hle,
    S15K.card_autFixedInG_five h15.h12 hcardE ht, Subgroup.zpowers (s : G), ?_, ?_, ?_⟩
  · intro h
    have : (s : G) ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers _
    exact hs1' (Subgroup.mem_bot.1 this)
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  · intro b hb
    have hbE : b ∈ E ⊓ Subgroup.centralizer (kZero p E t : Set G) := by
      rw [hcent]
      exact hb
    have hcomm : Commute b (s : G) := (Subgroup.mem_centralizer_iff.1 hbE.2 (s : G) hsK).symm
    have : b ∈ Subgroup.centralizer ((Subgroup.zpowers (s : G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact ((Commute.zpow_right hcomm n).eq).symm
    exact Subgroup.centralizer_le_normalizer _ this

theorem D_le_autFixedInG (hS : SchreierFor InCatalog) (h82 : LocalThetaComponentEmbeddingFrontier)
    (h15 : Sec15Hyp G p A c L E) {f : ℕ} {t : MulAut E} (hAtt : KFAt p E f t) {e : G}
    (he1 : e ≠ 1) (het : e ∈ autFixedInG E t) {D : Subgroup G}
    (hD : ∀ x : G, x ∈ D ↔ x ∈ E ∧ ∀ l ∈ thetaLayer p e, x * l * x⁻¹ * l⁻¹ ∈ thetaCore p e) :
    D ≤ autFixedInG E t := by
  classical
  have h := h15.h12
  have hp := h.prime
  have hmod := hAtt.2.1
  have hq : CFSG.IsQuasisimple ↥(kZero p E t) := S13K.isQuasisimple_of_model_psl_two hmod
  have hKc : Subgroup.center ↥(kZero p E t) = ⊥ :=
    (S13K.isQuasisimple_and_center_of_model_psl_two hmod).2
  have hKe : kZero p E t ≤ Subgroup.centralizer ({e} : Set G) := by
    intro k hk
    have : e ∈ E ⊓ Subgroup.centralizer (kZero p E t : Set G) := by
      rw [hAtt.2.2.1]
      exact het
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 this.2 k hk)
  have hKL : kZero p E t ≤ thetaLayer p e := K159.kZero_le_thetaLayer hS h82 h hq het he1
  have hbot := kZero_inf_thetaCore_eq_bot hp hq hKc hKe
  intro x hx
  obtain ⟨hxE, hxl⟩ := (hD x).1 hx
  have hcentx : x ∈ E ⊓ Subgroup.centralizer (kZero p E t : Set G) := by
    refine ⟨hxE, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    have h1 : x * k * x⁻¹ * k⁻¹ ∈ kZero p E t ⊓ thetaCore p e := by
      refine ⟨?_, hxl k (hKL hk)⟩
      have hxN := S13K.E_le_normalizer_kZero h.E_elem t hxE
      exact (kZero p E t).mul_mem ((Subgroup.mem_normalizer_iff.1 hxN k).1 hk)
        ((kZero p E t).inv_mem hk)
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : x * k = k * x := mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)
    exact h2.symm
  rw [← hAtt.2.2.1]
  exact hcentx

theorem card_E_inf_I_ge (hMod : KFU5Mod) (hAt : KFU5At) (h15 : Sec15Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hout : Outcome152Five p E A (lieGenerated p E)) :
    p ^ 3 ≤ Nat.card ↥(E ⊓ lieGenerated p E) := by
  classical
  have h := h15.h12
  have hp := h.prime
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  have hE : ∀ e : ↥E, e ^ p = 1 := fun e =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.1 (IsElementaryAbelian.exponent_dvd_p p ↥E) e
  obtain ⟨M⟩ := Sec153.nonempty_modData hMod h15 hF hout
  obtain ⟨f₀, hf₀, hpf₀, ⟨e₀⟩, -, hcardE, -⟩ := id hout
  let D' : Subgroup ↥E := (lieGenerated p E).comap E.subtype
  have hdiff : ∀ i j : Fin 5, M.v j * (M.v i)⁻¹ ∈ D' := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [mul_inv_cancel]
      exact D'.one_mem
    · obtain ⟨t, ht, hθ⟩ := Sec153.exists_reflection_swap hp M.θ M.refl i j hij
      obtain ⟨hne, hmod, hcent, hmoved, k, hk, hkK, hkt⟩ :=
        hAt G p A c L E f₀ h15 hF hout hf₀ hpf₀ ⟨e₀⟩ t ht
      have hKI : kZero p E t ≤ lieGenerated p E :=
        le_sSup ⟨t, ht, (isKt_iff_of_nonexceptional hne).2 rfl⟩
      have h1 : t (M.v i) = M.v j := by
        have := M.perm ⟨t, Subgroup.subset_closure ht⟩ i
        rw [hθ, Equiv.swap_apply_left] at this
        exact this
      have h2 : ((t (M.v i) * (M.v i)⁻¹ : ↥E) : G) ∈ kZero p E t :=
        hmoved ⟨t (M.v i) * (M.v i)⁻¹, Subgroup.subset_closure ⟨M.v i, rfl⟩, rfl⟩
      rw [h1] at h2
      exact hKI h2
  have hnorm : D'.Normal := ⟨fun n hn g => by rw [hEc g n, mul_inv_cancel_right]; exact hn⟩
  set g : ↥E ⧸ D' := QuotientGroup.mk (M.v 0) with hg
  have hq : ∀ i, (QuotientGroup.mk (M.v i) : ↥E ⧸ D') = g := by
    intro i
    rw [QuotientGroup.eq]
    have := hdiff i 0
    rwa [hEc (M.v 0) (M.v i)⁻¹] at this
  have hgp : g ^ p = 1 := by
    rw [hg, ← QuotientGroup.mk_pow, hE, QuotientGroup.mk_one]
  have hcycl : (⊤ : Subgroup (↥E ⧸ D')) ≤ Subgroup.zpowers g := by
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, ha⟩ := M.gen x
    rw [ha]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, hq]
    rw [← zpow_add, ← zpow_add, ← zpow_add, ← zpow_add]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _
  have hcardQ : Nat.card (↥E ⧸ D') ≤ p := by
    have htop : Subgroup.zpowers g = ⊤ := le_antisymm le_top hcycl
    have h1 : Nat.card (↥E ⧸ D') = Nat.card ↥(Subgroup.zpowers g) := by
      rw [htop, Subgroup.card_top]
    rw [h1, Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
  have h4 : Nat.card ↥D' * D'.index = Nat.card ↥E := Subgroup.card_mul_index D'
  have h5 : D'.index = Nat.card (↥E ⧸ D') := rfl
  rw [hcardE] at h4
  have h6 : p ^ 4 ≤ Nat.card ↥D' * p := by
    rw [← h4]
    exact Nat.mul_le_mul_left _ (h5 ▸ hcardQ)
  have h7 : p ^ 3 ≤ Nat.card ↥D' := by
    have hpos : 0 < p := hp.pos
    have : p ^ 3 * p ≤ Nat.card ↥D' * p := by
      calc p ^ 3 * p = p ^ 4 := by ring
        _ ≤ _ := h6
    exact Nat.le_of_mul_le_mul_right this hpos
  have h8 : D'.map E.subtype = E ⊓ lieGenerated p E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxE, hxI⟩
      exact ⟨⟨x, hxE⟩, hxI, rfl⟩
  rw [← h8, Subgroup.card_map_of_injective E.subtype_injective]
  exact h7

omit [Finite G] in
theorem perfect_le_sup_of_commute' {I C Y₀ : Subgroup G} {e : G}
    (hIC : ∀ a ∈ I, ∀ b ∈ C, a * b = b * a)
    (heI : ∀ i ∈ I, ∀ d ∈ C, (i * d) * e = e * (i * d) → i * e = e * i)
    (hY₀ : ∀ P : Subgroup G, P ≤ I ⊓ Subgroup.centralizer ({e} : Set G) →
      Group.IsPerfect ↥P → P ≤ Y₀)
    {Y : Subgroup G} (hYperf : Group.IsPerfect ↥Y) (hYIC : Y ≤ I ⊔ C)
    (hYe : Y ≤ Subgroup.centralizer ({e} : Set G)) : Y ≤ Y₀ ⊔ C := by
  classical
  let SY : Subgroup G :=
    { carrier := {i | i ∈ I ∧ ∃ d ∈ C, i * d ∈ Y}
      mul_mem' := by
        rintro a b ⟨haI, d₁, hd₁, h₁⟩ ⟨hbI, d₂, hd₂, h₂⟩
        refine ⟨I.mul_mem haI hbI, d₁ * d₂, C.mul_mem hd₁ hd₂, ?_⟩
        have h := hIC b hbI d₁ hd₁
        have : a * b * (d₁ * d₂) = (a * d₁) * (b * d₂) := by
          calc a * b * (d₁ * d₂) = a * (b * d₁) * d₂ := by group
            _ = a * (d₁ * b) * d₂ := by rw [h]
            _ = (a * d₁) * (b * d₂) := by group
        rw [this]
        exact Y.mul_mem h₁ h₂
      one_mem' := ⟨I.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨haI, d, hd, h⟩
        refine ⟨I.inv_mem haI, d⁻¹, C.inv_mem hd, ?_⟩
        have h1 := hIC a haI d hd
        have : a⁻¹ * d⁻¹ = (a * d)⁻¹ := by
          calc a⁻¹ * d⁻¹ = (d * a)⁻¹ := by group
            _ = (a * d)⁻¹ := by rw [h1]
        rw [this]
        exact Y.inv_mem h }
  have hSYI : ∀ i ∈ SY, i ∈ I := fun i hi => hi.1
  have hSYe : ∀ i ∈ SY, i ∈ Subgroup.centralizer ({e} : Set G) := by
    rintro i ⟨hiI, d, hd, hid⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact heI i hiI d hd (Subgroup.mem_centralizer_singleton_iff.1 (hYe hid))
  set P : Subgroup G := ⁅SY, SY⁆ with hP
  have hPSY : P ≤ SY := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact SY.mul_mem (SY.mul_mem (SY.mul_mem ha hb) (SY.inv_mem ha)) (SY.inv_mem hb)
  have hPI : ∀ x ∈ P, x ∈ I := fun x hx => hSYI x (hPSY hx)
  have hPC : ∀ x ∈ P, ∀ y ∈ C, x * y = y * x := fun x hx y hy => hIC x (hPI x hx) y hy
  have hYPC : Y ≤ P ⊔ C := by
    calc Y = ⁅Y, Y⁆ := ((Subgroup.isPerfect_iff).1 hYperf).symm
      _ ≤ P ⊔ C := by
        rw [Subgroup.commutator_def]
        refine (Subgroup.closure_le _).2 ?_
        rintro _ ⟨y₁, hy₁, y₂, hy₂, rfl⟩
        obtain ⟨i₁, hi₁, d₁, hd₁, h₁⟩ := PlaneCommuting.exists_mul_of_mem_sup hIC (hYIC hy₁)
        obtain ⟨i₂, hi₂, d₂, hd₂, h₂⟩ := PlaneCommuting.exists_mul_of_mem_sup hIC (hYIC hy₂)
        have hi₁S : i₁ ∈ SY := ⟨hi₁, d₁, hd₁, h₁ ▸ hy₁⟩
        have hi₂S : i₂ ∈ SY := ⟨hi₂, d₂, hd₂, h₂ ▸ hy₂⟩
        rw [h₁, h₂, PlaneCommuting.commutatorElement_mul_mul hIC ⟨i₁, hi₁⟩ ⟨i₂, hi₂⟩
          ⟨d₁, hd₁⟩ ⟨d₂, hd₂⟩]
        refine Subgroup.mul_mem_sup (Subgroup.commutator_mem_commutator hi₁S hi₂S) ?_
        rw [commutatorElement_def]
        exact C.mul_mem (C.mul_mem (C.mul_mem hd₁ hd₂) (C.inv_mem hd₁)) (C.inv_mem hd₂)
  have hPperf : Group.IsPerfect ↥P := by
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) ?_
    · rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
    · refine Subgroup.commutator_le.2 fun i₁ hi₁ i₂ hi₂ => ?_
      obtain ⟨d₁, hd₁, hy₁⟩ := hi₁.2
      obtain ⟨d₂, hd₂, hy₂⟩ := hi₂.2
      obtain ⟨π₁, hπ₁, c₁, hc₁, e₁⟩ := PlaneCommuting.exists_mul_of_mem_sup hPC (hYPC hy₁)
      obtain ⟨π₂, hπ₂, c₂, hc₂, e₂⟩ := PlaneCommuting.exists_mul_of_mem_sup hPC (hYPC hy₂)
      have hn₁ : i₁ = π₁ * (c₁ * d₁⁻¹) := by
        calc i₁ = (i₁ * d₁) * d₁⁻¹ := by group
          _ = (π₁ * c₁) * d₁⁻¹ := by rw [e₁]
          _ = π₁ * (c₁ * d₁⁻¹) := by group
      have hn₂ : i₂ = π₂ * (c₂ * d₂⁻¹) := by
        calc i₂ = (i₂ * d₂) * d₂⁻¹ := by group
          _ = (π₂ * c₂) * d₂⁻¹ := by rw [e₂]
          _ = π₂ * (c₂ * d₂⁻¹) := by group
      have hc₁' : c₁ * d₁⁻¹ ∈ C := C.mul_mem hc₁ (C.inv_mem hd₁)
      have hc₂' : c₂ * d₂⁻¹ ∈ C := C.mul_mem hc₂ (C.inv_mem hd₂)
      have hn₂I : c₂ * d₂⁻¹ ∈ I := by
        have : c₂ * d₂⁻¹ = π₂⁻¹ * i₂ := by rw [hn₂]; group
        rw [this]
        exact I.mul_mem (I.inv_mem (hPI π₂ hπ₂)) (hSYI i₂ hi₂)
      have hcomm : ⁅c₁ * d₁⁻¹, c₂ * d₂⁻¹⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (hIC _ hn₂I _ hc₁').symm
      rw [hn₁, hn₂, PlaneCommuting.commutatorElement_mul_mul hIC ⟨π₁, hPI π₁ hπ₁⟩
        ⟨π₂, hPI π₂ hπ₂⟩ ⟨c₁ * d₁⁻¹, hc₁'⟩ ⟨c₂ * d₂⁻¹, hc₂'⟩]
      show ⁅π₁, π₂⁆ * ⁅c₁ * d₁⁻¹, c₂ * d₂⁻¹⁆ ∈ ⁅P, P⁆
      rw [hcomm, mul_one]
      exact Subgroup.commutator_mem_commutator hπ₁ hπ₂
  have hPY₀ : P ≤ Y₀ := hY₀ P (fun x hx => ⟨hPI x hx, hSYe x (hPSY hx)⟩) hPperf
  exact hYPC.trans (sup_le_sup_right hPY₀ C)

omit [Finite G] in
theorem heI_of_mem {I : Subgroup G} {e : G} (heI : e ∈ I) :
    ∀ i ∈ I, ∀ d ∈ Subgroup.centralizer (I : Set G), (i * d) * e = e * (i * d) → i * e = e * i := by
  intro i hi d hd h
  have h2 : e * d = d * e := Subgroup.mem_centralizer_iff.1 hd e heI
  have h3 : i * e * d = e * i * d := by
    calc i * e * d = i * (e * d) := by group
      _ = i * (d * e) := by rw [h2]
      _ = (i * d) * e := by group
      _ = e * (i * d) := h
      _ = e * i * d := by group
  exact mul_right_cancel h3

omit [Finite G] in
theorem heI_of_inf_eq_bot {I : Subgroup G} {e : G} (heN : e ∈ Subgroup.normalizer (I : Set G))
    (hZ : I ⊓ Subgroup.centralizer (I : Set G) = ⊥) :
    ∀ i ∈ I, ∀ d ∈ Subgroup.centralizer (I : Set G), (i * d) * e = e * (i * d) → i * e = e * i := by
  intro i hi d hd h
  have hi' : e * i * e⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 heN i).1 hi
  have hd' : e * d * e⁻¹ ∈ Subgroup.centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : e⁻¹ * g * e ∈ I := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (I : Set G)).inv_mem heN) g).1 hg
      simpa using this
    have := Subgroup.mem_centralizer_iff.1 hd _ hg'
    calc g * (e * d * e⁻¹) = e * ((e⁻¹ * g * e) * d) * e⁻¹ := by group
      _ = e * (d * (e⁻¹ * g * e)) * e⁻¹ := by rw [this]
      _ = e * d * e⁻¹ * g := by group
  have h1 : e * i * e⁻¹ * (e * d * e⁻¹) = i * d := by
    have : e * (i * d) * e⁻¹ = i * d := by
      rw [← h]
      group
    rw [← this]
    group
  have h2 : i⁻¹ * (e * i * e⁻¹) = d * (e * d * e⁻¹)⁻¹ := by
    have h3 : i⁻¹ * (e * i * e⁻¹ * (e * d * e⁻¹)) = d := by
      rw [h1]
      group
    calc i⁻¹ * (e * i * e⁻¹) = i⁻¹ * (e * i * e⁻¹ * (e * d * e⁻¹)) * (e * d * e⁻¹)⁻¹ := by group
      _ = d * (e * d * e⁻¹)⁻¹ := by rw [h3]
  have hmemI : i⁻¹ * (e * i * e⁻¹) ∈ I := I.mul_mem (I.inv_mem hi) hi'
  have hmemC : i⁻¹ * (e * i * e⁻¹) ∈ Subgroup.centralizer (I : Set G) := by
    rw [h2]
    exact (Subgroup.centralizer (I : Set G)).mul_mem hd
      ((Subgroup.centralizer (I : Set G)).inv_mem hd')
  have hbot : i⁻¹ * (e * i * e⁻¹) = 1 := by
    have : i⁻¹ * (e * i * e⁻¹) ∈ I ⊓ Subgroup.centralizer (I : Set G) := ⟨hmemI, hmemC⟩
    rw [hZ, Subgroup.mem_bot] at this
    exact this
  have h4 : e * i * e⁻¹ = i := by
    have := congrArg (fun z => i * z) hbot
    simpa using this
  calc i * e = e * i * e⁻¹ * e := by rw [h4]
    _ = e * i := by group

theorem kf1510E_of_gen (hS : SchreierFor InCatalog) (h82 : LocalThetaComponentEmbeddingFrontier)
    (hMod : KFU5Mod) (hAt : KFU5At) (hEin : U5EInndiag) (hLR5 : S15K.LayerRowFive)
    (hPerf : K159.KFPerfNormalizerFive) (hGen : K159.KFCompGenFive)
    (hGA : CFSG.Open.GriessAllModelsStatement) : KF1510E := by
  intro G _ _ p A c L E h15 hF hout e he he1 _ hLN D hD
  classical
  have h := h15.h12
  have hp := h.prime
  obtain ⟨f, hf, hpf, ⟨e₀⟩, -, hcardE, -⟩ := id hout
  by_cases hN : ∃ t ∈ reflectionSet p E, e ∈ autFixedInG E t
  ·
    obtain ⟨t, ht, het⟩ := hN
    have hAtt : KFAt p E f t := hAt G p A c L E f h15 hF hout hf hpf ⟨e₀⟩ t ht
    exact Or.inr (Or.inr ⟨autFixedInG E t, autFixedInG_mem_admissible h15 hcardE ht hAtt,
      D_le_autFixedInG hS h82 h15 hAtt he1 het hD⟩)
  ·
    push Not at hN
    refine Or.inr (Or.inl ?_)
    set I := lieGenerated p E with hI
    set C := Subgroup.centralizer (I : Set G) with hC
    have hLD : S15K.LayerDataW p E I := hLR5 G p A c L E h15 hF hout
    obtain ⟨ι, Q, hQH, hQc, hperf, -⟩ := hLD e he he1
    have hempty : {x : G | ∃ t ∈ reflectionSet p E, ∃ K : Subgroup G, IsKt p E t K ∧
        K ≤ Subgroup.centralizer ({e} : Set G) ∧ x ∈ K} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      obtain ⟨t, ht, K, hK, hKC, -⟩ := hx
      have hAtt : KFAt p E f t := hAt G p A c L E f h15 hF hout hf hpf ⟨e₀⟩ t ht
      have hKeq : K = kZero p E t := (isKt_iff_of_nonexceptional hAtt.1).1 hK
      have : e ∈ E ⊓ Subgroup.centralizer (kZero p E t : Set G) := by
        refine ⟨he, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
        rw [← hKeq] at hk
        exact Subgroup.mem_centralizer_singleton_iff.1 (hKC hk)
      rw [hAtt.2.2.1] at this
      exact hN t ht this
    have hQbot : ∀ i, Q i ≤ ⊥ := fun i => by
      have := hGen G p A c L E h15 hF hout e he he1 (Q i) (hQH i) (hQc i)
      rwa [hempty, Subgroup.closure_empty] at this
    have hY₀ : ∀ P : Subgroup G, P ≤ I ⊓ Subgroup.centralizer ({e} : Set G) →
        Group.IsPerfect ↥P → P ≤ ⊥ := fun P hP hPperf => (hperf P hP hPperf).trans (iSup_le hQbot)
    have hEN : E ≤ Subgroup.normalizer (I : Set G) := E_le_lieNormalizer h15
    have heI : ∀ i ∈ I, ∀ d ∈ C, (i * d) * e = e * (i * d) → i * e = e * i := by
      by_cases heIm : e ∈ I
      · exact heI_of_mem heIm
      · have hp5 : p = 5 := by
          by_contra hne
          exact heIm (Sec153.E_le_of_ne_five hMod hAt G p A c L E h15 hF hout hne he)
        have hZ := center_lieGenerated_eq_bot_five hGA hEin h15 hF hout hp5
        have hcard : Nat.card ↥(I ⊓ Subgroup.centralizer (I : Set G)) = 1 := by
          rw [← card_center_eq_card_inf, hZ, Subgroup.card_bot]
        exact heI_of_inf_eq_bot (hEN he) (Subgroup.eq_bot_of_card_eq _ hcard)
    have hIC : ∀ a ∈ I, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
      Subgroup.mem_centralizer_iff.1 hb a ha
    have hZC : ∀ Z ∈ thetaComponentsAt p e, Z ≤ C := by
      intro Z hZ
      have hperfZ : Group.IsPerfect ↥Z := isPerfect_of_mem_thetaComponentsAt hZ
      have hZIC : Z ≤ I ⊔ C := hPerf G p A c L E h15 hF hout Z hperfZ (hLN Z hZ)
      have hZe : Z ≤ Subgroup.centralizer ({e} : Set G) := (mem_thetaComponentsAt_iff.1 hZ).1
      have := perfect_le_sup_of_commute' hIC heI hY₀ hperfZ hZIC hZe
      rwa [bot_sup_eq] at this
    have hLC : thetaLayer p e ≤ C := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨Z, hZ, hxZ⟩
      exact hZC Z hZ hxZ
    have hED : E ⊓ I ≤ D := by
      rintro x ⟨hxE, hxI⟩
      refine (hD x).2 ⟨hxE, fun l hl => ?_⟩
      have h1 : x * l = l * x := Subgroup.mem_centralizer_iff.1 (hLC hl) x hxI
      have : x * l * x⁻¹ * l⁻¹ = 1 := by
        rw [h1]
        group
      rw [this]
      exact Subgroup.one_mem _
    exact (card_E_inf_I_ge hMod hAt h15 hF hout).trans (Subgroup.card_le_of_le hED)

end CFSG.RankThree.PartOne.U5E
