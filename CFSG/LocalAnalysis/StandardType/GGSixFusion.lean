module

public import CFSG.Assembly.Defs
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Open.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type*} [Group G]

@[expose] def GGControlsStrongFusion (H E : Subgroup G) : Prop :=
  E ≤ H ∧ ∀ g : G, E.map (MulAut.conj g⁻¹).toMonoidHom ⊓ H ≠ ⊥ → g ∈ H

theorem ggControlsStrongFusion_iff {H E : Subgroup G} :
    GGControlsStrongFusion H E ↔
      E ≤ H ∧ ∀ e ∈ E, e ≠ 1 → ∀ g : G, g⁻¹ * e * g ∈ H → g ∈ H := by
  constructor
  · rintro ⟨hEH, h⟩
    refine ⟨hEH, fun e he he1 g hg => h g ?_⟩
    rw [Ne, Subgroup.eq_bot_iff_forall]
    push Not
    refine ⟨g⁻¹ * e * g, Subgroup.mem_inf.mpr ⟨Subgroup.mem_map.mpr ⟨e, he, ?_⟩, hg⟩, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    · intro h1
      apply he1
      calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
  · rintro ⟨hEH, h⟩
    refine ⟨hEH, fun g hg => ?_⟩
    rw [Ne, Subgroup.eq_bot_iff_forall] at hg
    push Not at hg
    obtain ⟨y, hy, hy1⟩ := hg
    obtain ⟨hyE, hyH⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hyE
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hyH hy1
    refine h e he ?_ g hyH
    rintro rfl
    exact hy1 (by group)

namespace GGControlsStrongFusion

variable {H E : Subgroup G}

theorem mem_of_conj_mem (h : GGControlsStrongFusion H E) {e : G} (he : e ∈ E) (he1 : e ≠ 1)
    {g : G} (hg : g⁻¹ * e * g ∈ H) : g ∈ H :=
  (ggControlsStrongFusion_iff.mp h).2 e he he1 g hg

theorem centralizer_le (h : GGControlsStrongFusion H E) {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    Subgroup.centralizer {e} ≤ H := by
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff] at hg
  refine h.mem_of_conj_mem he he1 ?_
  have : g⁻¹ * e * g = e := by rw [mul_assoc, ← hg, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [this]
  exact h.1 he

theorem le_of_isSubnormal (h : GGControlsStrongFusion H E) {e : G} (he : e ∈ E) (he1 : e ≠ 1)
    {R X : Subgroup G} (heR : e ∈ R) (hRH : R ≤ H) (hRX : IsSubnormal R X) : X ≤ H := by
  induction hRX with
  | refl => exact hRH
  | @step R' N K hle hN _ ih =>
    refine ih (hle heR) fun n hn => h.mem_of_conj_mem he he1 (hRH ?_)
    have hc := hN.conj_mem ⟨e, hle heR⟩ (Subgroup.mem_subgroupOf.mpr heR) (⟨n, hn⟩ : N)⁻¹
    rw [Subgroup.mem_subgroupOf] at hc
    simpa using hc

end GGControlsStrongFusion

theorem mem_zpowers_of_orderOf_prime {e y : G} (he : (orderOf e).Prime)
    (hy : y ∈ Subgroup.zpowers e) (hy1 : y ≠ 1) : e ∈ Subgroup.zpowers y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hpow : (e ^ k) ^ orderOf e = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
      one_zpow]
  have hord : orderOf (e ^ k) = orderOf e := by
    rcases (Nat.dvd_prime he).mp (orderOf_dvd_of_pow_eq_one hpow) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have hfin : Finite (Subgroup.zpowers e) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; exact he.ne_zero)
  have heq : Subgroup.zpowers (e ^ k) = Subgroup.zpowers e :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  rw [heq]
  exact Subgroup.mem_zpowers e

theorem ggControlsStrongFusion_zpowers_iff {H : Subgroup G} {e : G} (he : (orderOf e).Prime) :
    GGControlsStrongFusion H (Subgroup.zpowers e) ↔
      e ∈ H ∧ ∀ g : G, g⁻¹ * e * g ∈ H → g ∈ H := by
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at he
    exact Nat.not_prime_one he
  rw [ggControlsStrongFusion_iff, Subgroup.zpowers_le]
  refine ⟨fun h => ⟨h.1, fun g hg => h.2 e (Subgroup.mem_zpowers e) he1 g hg⟩,
    fun h => ⟨h.1, fun y hy hy1 g hg => h.2 g ?_⟩⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_orderOf_prime he hy hy1)
  have : g⁻¹ * e * g = (g⁻¹ * y * g) ^ m := by
    rw [← hm]
    have h := map_zpow (MulAut.conj g⁻¹) y m
    simp only [MulAut.conj_apply, inv_inv] at h
    exact h
  rw [this]
  exact H.zpow_mem hg m

theorem mem_of_conj_eq_conj {H : Subgroup G} {e g h : G} (hC : Subgroup.centralizer {e} ≤ H)
    (hH : h ∈ H) (heq : g⁻¹ * e * g = h⁻¹ * e * h) : g ∈ H := by
  have hc : g * h⁻¹ ∈ Subgroup.centralizer {e} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * h⁻¹ * e = g * (h⁻¹ * e * h) * h⁻¹ := by group
      _ = g * (g⁻¹ * e * g) * h⁻¹ := by rw [heq]
      _ = e * (g * h⁻¹) := by group
  have := H.mul_mem (hC hc) hH
  rwa [inv_mul_cancel_right] at this

theorem ggControlsStrongFusion_zpowers_of_fusion {H : Subgroup G} {e : G}
    (he : (orderOf e).Prime) (heH : e ∈ H) (hC : Subgroup.centralizer {e} ≤ H)
    (hfus : ∀ g : G, g⁻¹ * e * g ∈ H → ∃ h ∈ H, g⁻¹ * e * g = h⁻¹ * e * h) :
    GGControlsStrongFusion H (Subgroup.zpowers e) := by
  refine (ggControlsStrongFusion_zpowers_iff he).mpr ⟨heH, fun g hg => ?_⟩
  obtain ⟨h, hH, heq⟩ := hfus g hg
  exact mem_of_conj_eq_conj hC hH heq

theorem mem_of_sq_eq_one_of_odd_relIndex {G₀ M : Subgroup G} (hN : (G₀.subgroupOf M).Normal)
    (hodd : Odd (G₀.relIndex M)) {t : G} (htM : t ∈ M) (ht : t ^ 2 = 1) : t ∈ G₀ := by
  let q : ↥M ⧸ G₀.subgroupOf M := QuotientGroup.mk ⟨t, htM⟩
  have h2 : orderOf q ∣ 2 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    have : (⟨t, htM⟩ : M) ^ 2 = 1 := Subtype.ext (by simpa using ht)
    rw [← QuotientGroup.mk_pow, this, QuotientGroup.mk_one]
  have hidx : orderOf q ∣ G₀.relIndex M := by
    have := orderOf_dvd_natCard q
    rwa [← Subgroup.index_eq_card] at this
  have h1 : orderOf q = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr hodd) h2 hidx
  have hq : q = 1 := orderOf_eq_one_iff.mp h1
  have hmem : (⟨t, htM⟩ : M) ∈ G₀.subgroupOf M := (QuotientGroup.eq_one_iff _).mp hq
  exact Subgroup.mem_subgroupOf.mp hmem

theorem exists_sylow_two_map_eq_of_odd_relIndex [Finite G] {G₀ M : Subgroup G} (hle : G₀ ≤ M)
    (hodd : Odd (G₀.relIndex M)) (T : Sylow 2 G₀) :
    ∃ T' : Sylow 2 M, (T' : Subgroup M).map M.subtype = (T : Subgroup G₀).map G₀.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := (T : Subgroup G₀).map G₀.subtype with hPdef
  have hPG₀ : P ≤ G₀ := Subgroup.map_subtype_le _
  have hPp : IsPGroup 2 P := T.isPGroup'.map G₀.subtype
  have hP'p : IsPGroup 2 (P.subgroupOf M) :=
    hPp.comap_of_injective M.subtype Subtype.coe_injective
  have hPT : P.subgroupOf G₀ = (T : Subgroup G₀) :=
    Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _
  have hidx : ¬ 2 ∣ (P.subgroupOf M).index := by
    have h1 := Subgroup.relIndex_mul_relIndex P G₀ M hPG₀ hle
    have h2 : P.relIndex G₀ = (T : Subgroup G₀).index := by
      rw [Subgroup.relIndex, hPT]
    change ¬ 2 ∣ P.relIndex M
    rw [← h1, h2]
    intro h
    rcases (Nat.prime_two.dvd_mul).mp h with h | h
    · exact T.not_dvd_index h
    · exact Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd) h
  refine ⟨hP'p.toSylow hidx, ?_⟩
  change (P.subgroupOf M).map M.subtype = P
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
  exact hPG₀.trans hle

theorem isElemAbelian_map_hom {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) (f : G →* G) :
    IsElemAbelian p (E.map f) := CFSG.Open.IsElemAbelian.map hE _

theorem mem_normalizer_of_map_conj_eq {H : Subgroup G} {x : G}
    (h : H.map (MulAut.conj x).toMonoidHom = H) : x ∈ Subgroup.normalizer (H : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => ?_, fun ha => ?_⟩
  · rw [← h]
    exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  · rw [← h] at ha
    obtain ⟨a', ha', heq⟩ := Subgroup.mem_map.mp ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at heq
    have : a' = a := by
      have := congrArg (fun y => x⁻¹ * y * x) heq
      simpa [mul_assoc] using this
    rwa [← this]

theorem exists_mem_normalizer_conj_eq [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (P : Sylow p G)
    (huniq : ∀ E : Subgroup G, E ≤ (P : Subgroup G) → IsElemAbelian p E →
      Nat.card E = Nat.card Bs → E = Bs)
    {b g : G} (hb : b ∈ Bs) (hg : g⁻¹ * b * g ∈ Bs) :
    ∃ n ∈ Subgroup.normalizer (Bs : Set G), g⁻¹ * b * g = n⁻¹ * b * n := by
  have hcomm : ∀ a ∈ Bs, ∀ c ∈ Bs, a * c = c * a := by
    have := hBs.1
    intro a ha c hc
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Bs) ⟨c, hc⟩)
  set b' := g⁻¹ * b * g with hb'
  set C := Subgroup.centralizer ({b'} : Set G) with hC
  have hBC : Bs ≤ C := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a ha b' hg)
  set Bg := Bs.map (MulAut.conj g⁻¹).toMonoidHom with hBg
  have hBgC : Bg ≤ C := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hb']
    have := hcomm a ha b hb
    calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [this]
      _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group
  have hBsp : IsPGroup p Bs := fun a => ⟨1, Subtype.ext (by simpa using hBs.2 a a.2)⟩
  have hBgp : IsPGroup p Bg := hBsp.map _
  obtain ⟨S, hS⟩ := (hBsp.comap_of_injective C.subtype Subtype.coe_injective).exists_le_sylow
  obtain ⟨S₂, hS₂⟩ := (hBgp.comap_of_injective C.subtype Subtype.coe_injective).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S₂ S
  set SG : Subgroup G := (S : Subgroup C).map C.subtype with hSG
  have hBsSG : Bs ≤ SG := fun a ha =>
    Subgroup.mem_map.mpr ⟨⟨a, hBC ha⟩, hS (Subgroup.mem_comap.mpr ha), rfl⟩
  have hBgSG : Bg.map (MulAut.conj (c : G)).toMonoidHom ≤ SG := by
    rintro _ ⟨a, ha, rfl⟩
    have haS₂ : (⟨a, hBgC ha⟩ : C) ∈ (S₂ : Subgroup C) := hS₂ (Subgroup.mem_comap.mpr ha)
    have hmem : (MulAut.conj c) ⟨a, hBgC ha⟩ ∈ ((c • S₂ : Sylow p C) : Subgroup C) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ haS₂
    rw [hc] at hmem
    exact Subgroup.mem_map.mpr ⟨_, hmem, by simp [MulAut.conj_apply]⟩
  obtain ⟨P', hP'⟩ := (S.isPGroup'.map C.subtype).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P' P
  have key : ∀ E : Subgroup G, E ≤ (P' : Subgroup G) →
      E.map (MulAut.conj h).toMonoidHom ≤ (P : Subgroup G) := by
    intro E hE
    rintro _ ⟨a, ha, rfl⟩
    have hmem : (MulAut.conj h) a ∈ ((h • P' : Sylow p G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hE ha)
    rwa [hh] at hmem
  have h1 : Bs.map (MulAut.conj h).toMonoidHom = Bs :=
    huniq _ (key _ (hBsSG.trans hP')) (isElemAbelian_map_hom hBs _)
      (Subgroup.card_map_of_injective (MulAut.conj h).injective)
  have h2 : (Bg.map (MulAut.conj (c : G)).toMonoidHom).map (MulAut.conj h).toMonoidHom = Bs := by
    refine huniq _ (key _ (hBgSG.trans hP'))
      (isElemAbelian_map_hom (isElemAbelian_map_hom (isElemAbelian_map_hom hBs _) _) _) ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective,
      Subgroup.card_map_of_injective (MulAut.conj (c : G)).injective,
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hcomp : (Bg.map (MulAut.conj (c : G)).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      Bs.map (MulAut.conj (h * ((c : G) * g⁻¹))).toMonoidHom := by
    rw [hBg, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  have hhN : h ∈ Subgroup.normalizer (Bs : Set G) := mem_normalizer_of_map_conj_eq h1
  have hkN : h * ((c : G) * g⁻¹) ∈ Subgroup.normalizer (Bs : Set G) :=
    mem_normalizer_of_map_conj_eq (hcomp ▸ h2)
  have hcgN : (c : G) * g⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hhN) hkN
    rwa [inv_mul_cancel_left] at this
  refine ⟨g * (c : G)⁻¹, ?_, ?_⟩
  · have := Subgroup.inv_mem _ hcgN
    simpa using this
  · have hcb : (c : G) * b' = b' * (c : G) := by
      have := c.2
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    calc g⁻¹ * b * g = b' := rfl
      _ = (c : G) * b' * (c : G)⁻¹ := by rw [hcb, mul_inv_cancel_right]
      _ = (g * (c : G)⁻¹)⁻¹ * b * (g * (c : G)⁻¹) := by rw [hb']; group

theorem mem_of_mem_centralizer_of_maximal [Finite G] {p : ℕ} {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hmax : ∀ E : Subgroup G, IsElemAbelian p E → Nat.card E ≤ Nat.card Bs) {e : G}
    (he : e ∈ Subgroup.centralizer (Bs : Set G)) (hep : e ^ p = 1) : e ∈ Bs := by
  by_contra hne
  have hBsC : Bs ≤ Subgroup.centralizer (Bs : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hBs.1
  have heC : Subgroup.zpowers e ≤ Subgroup.centralizer (Bs : Set G) := Subgroup.zpowers_le.mpr he
  have heE : Subgroup.zpowers e ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  set E : Subgroup G := Bs ⊔ Subgroup.zpowers e with hE
  have hEC : E ≤ Subgroup.centralizer (E : Set G) := by
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mpr (sup_le hBsC heC)
    · exact Subgroup.le_centralizer_iff.mpr (sup_le (Subgroup.le_centralizer_iff.mp heC) heE)
  have hEcomm : IsMulCommutative E := Subgroup.le_centralizer_iff_isMulCommutative.mp hEC
  let K : Subgroup G :=
    { carrier := {y | y ∈ E ∧ y ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, hap⟩ ⟨hb, hbp⟩
        refine ⟨E.mul_mem ha hb, ?_⟩
        have hab : Commute a b :=
          ((Subgroup.mem_centralizer_iff.mp (hEC ha)) b hb).symm
        rw [hab.mul_pow, hap, hbp, one_mul]
      one_mem' := ⟨E.one_mem, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, hap⟩
        exact ⟨E.inv_mem ha, by rw [inv_pow, hap, inv_one]⟩ }
  have hEK : E ≤ K := by
    refine sup_le (fun a ha => ⟨le_sup_left (a := Bs) ha, hBs.2 a ha⟩) ?_
    rw [Subgroup.zpowers_le]
    exact ⟨le_sup_right (a := Bs) (Subgroup.mem_zpowers e), hep⟩
  have hEab : IsElemAbelian p E := ⟨hEcomm, fun y hy => (hEK hy).2⟩
  have hlt : Bs < E := by
    refine lt_of_le_of_ne le_sup_left fun h => hne ?_
    rw [h]
    exact le_sup_right (a := Bs) (Subgroup.mem_zpowers e)
  exact absurd (hmax E hEab) (not_le.mpr (Subgroup.card_lt_of_lt hlt))

theorem exists_sylow_eq_map_of_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (P : Sylow p M)
    (hN : Subgroup.normalizer (((P : Subgroup M).map M.subtype : Subgroup G) : Set G) ≤ M) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = (P : Subgroup M).map M.subtype := by
  set P₀ : Subgroup G := (P : Subgroup M).map M.subtype with hP₀
  have hP₀p : IsPGroup p P₀ := P.isPGroup'.map M.subtype
  obtain ⟨n, hn⟩ := hP₀p.exists_card_eq
  have hmod := Sylow.card_quotient_normalizer_modEq_card_quotient hn
  have hPM : P₀.subgroupOf M = (P : Subgroup M) :=
    Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _
  have hrel : ¬ p ∣ P₀.relIndex (Subgroup.normalizer (P₀ : Set G)) := by
    intro h
    have h1 := Subgroup.relIndex_mul_relIndex P₀ (Subgroup.normalizer (P₀ : Set G)) M
      Subgroup.le_normalizer hN
    have h2 : p ∣ P₀.relIndex M := h1 ▸ Dvd.dvd.mul_right h _
    rw [Subgroup.relIndex, hPM] at h2
    exact P.not_dvd_index h2
  have hidx : ¬ p ∣ P₀.index := by
    intro h
    apply hrel
    have h' : p ∣ Nat.card (G ⧸ P₀) := by rwa [← Subgroup.index_eq_card]
    exact (hmod.dvd_iff (dvd_refl p)).mpr h'
  exact ⟨hP₀p.toSylow hidx, rfl⟩

end CFSG.StandardType
