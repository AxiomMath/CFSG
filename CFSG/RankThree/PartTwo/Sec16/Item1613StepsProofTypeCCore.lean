module

public import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofTypeCModel
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item138ProofSylow
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec15.NoModNineTools
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec6.Item612Plus

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Type

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec19 CFSG.RankThree.PartTwo.Sec19.Step1914MoreSProof
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup GeneralLinearGroup)

variable {G : Type} [Group G] [Finite G]

theorem exists_typeC_core {L E : Subgroup G} {c x d : G}
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hLc : ∀ l ∈ L, l * c = c * l)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27)
    (hEeq : E = Subgroup.zpowers c ⊔ (E ⊓ L)) (hB9 : Nat.card (E ⊓ L : Subgroup G) = 9)
    (hx3 : x ^ 3 = 1) (hxc : x * c = c * x) (hxE : x ∉ E)
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hdE : d ∈ E) (hdx : x * d = d * x)
    {p f : ℕ} {K : Type} [Field K] (hK : PiField true p f K) (hq : ModThree true (p ^ f))
    (h4 : p ^ f = 4) (e : L ⧸ aschbacherSolvableCore 3 L ≃* projImage (slPi true 3 (p ^ f) K))
    {y : GL (Fin 3) K}
    (hxy : ∀ z : L ⧸ aschbacherSolvableCore 3 L,
      ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) z) :
        projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk y * (e z : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk y)⁻¹)
    (hrank : ∀ W : Subgroup G, W ≤ E ⊔ Subgroup.zpowers x → CFSG.Assembly.IsElemAbelian 3 W →
      Nat.card W = 81 → False) :
    ∃ F : Subgroup G, F ≤ E ⊔ Subgroup.zpowers x ∧ c ∈ F ∧ d ∈ F ∧
      CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
      Late.sectionCentralizer F L ((aschbacherSolvableCore 3 L).map L.subtype) =
        (Subgroup.zpowers c : Set G) ∧
      Sec4.IsTypeCOn F L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hK.finite
  have hK4 : Nat.card K = 4 := by rw [hK.card, h4]; rfl
  have hq2 : 2 < p ^ f := by omega
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (ProjGenLinGroup.mk : GL (Fin 3) K →* _) ProjGenLinGroup.mk_surjective
  have hcE : c ∈ E := hEeq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hSLn : (slPi true 3 (p ^ f) K).Normal := ⟨fun s hs g => by
    rw [Sec4.mem_slPi_true] at hs ⊢
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hs, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]⟩
  have hPSn : (projImage (slPi true 3 (p ^ f) K)).Normal :=
    hSLn.map ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  set κ : ProjGenLinGroup (Fin 3) K →* MulAut (projImage (slPi true 3 (p ^ f) K)) :=
    MulAut.conjNormal with hκdef
  have hκapp : ∀ (w : ProjGenLinGroup (Fin 3) K) (m : projImage (slPi true 3 (p ^ f) K)),
      ((κ w m : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        w * m * w⁻¹ := fun w m =>
    MulAut.conjNormal_apply w m
  have hκ : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    refine eq_one_of_conj_eq_self hK hq hq2 fun s hs => ?_
    have h1 := congrArg (fun σ : MulAut (projImage (slPi true 3 (p ^ f) K)) =>
      ((σ ⟨s, hs⟩ : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K)) hw
    simpa [hκapp] using h1
  set act : Subgroup.normalizer (L : Set G) →* MulAut (projImage (slPi true 3 (p ^ f) K)) :=
    (MulAut.congr e).toMonoidHom.comp ((Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom)
    with hactdef
  have hact : ∀ (g : Subgroup.normalizer (L : Set G)) (m : projImage (slPi true 3 (p ^ f) K)),
      act g m = e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom g) (e.symm m)) :=
    fun _ _ => rfl
  have hactL : ∀ (l : G) (hl : l ∈ L) (hlN : l ∈ Subgroup.normalizer (L : Set G)),
      act ⟨l, hlN⟩ = κ ((e (⟨l, hl⟩ : L) : projImage (slPi true 3 (p ^ f) K)) :
        ProjGenLinGroup (Fin 3) K) := by
    intro l hl hlN
    ext m
    rw [hact, hκapp, Sec15.thetaQuotMulAut_eq_conj hlN ⟨l, hl⟩ (fun _ => rfl), map_mul, map_mul,
      map_inv, MulEquiv.apply_symm_apply]
    rfl
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      hLc l hl)
  have hnc : L.normalizerMonoidHom ⟨c, hcN⟩ = 1 := by
    ext l
    rw [Sec4.normalizerMonoidHom_apply_coe, ← hLc l l.2, mul_inv_cancel_right]
    rfl
  have hactc : act ⟨c, hcN⟩ = 1 := by
    rw [hactdef, MonoidHom.comp_apply, MonoidHom.comp_apply, hnc, map_one, map_one]
  have hactx : act ⟨x, hx⟩ = κ (ProjGenLinGroup.mk y) := by
    ext m
    rw [hact, hκapp, hxy, MulEquiv.apply_symm_apply]
  set P := E ⊔ Subgroup.zpowers x with hPdef
  have hPN' : P ≤ Subgroup.normalizer (L : Set G) := sup_le hEN (Subgroup.zpowers_le.mpr hx)
  have hx1 : x ≠ 1 := fun h1 => hxE (h1 ▸ E.one_mem)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxo]
  have hP81 : Nat.card P = 81 := by
    have hN : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set G) :=
      Subgroup.zpowers_le.mpr hxNE
    have hcard := Sec6.card_sup_mul_card_inf hN
    have hinf : Subgroup.zpowers x ⊓ E = ⊥ := by
      have hdvd : Nat.card (Subgroup.zpowers x ⊓ E : Subgroup G) ∣ 3 := by
        have h1 := Subgroup.card_dvd_of_le
          (inf_le_left : Subgroup.zpowers x ⊓ E ≤ Subgroup.zpowers x)
        rwa [hcardx] at h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have heq : Subgroup.zpowers x ⊓ E = Subgroup.zpowers x :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcardx])
        have hxx : x ∈ Subgroup.zpowers x ⊓ E := by
          rw [heq]
          exact Subgroup.mem_zpowers _
        exact hxE hxx.2
    rw [hinf, Subgroup.card_bot, mul_one, hcardx, hE27, sup_comm] at hcard
    rw [hPdef]
    omega
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by rw [hP81]; norm_num)
  set S : Subgroup G := (κ.range.comap act).map (Subgroup.normalizer (L : Set G)).subtype
    with hSdef
  have hmemS : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)), act ⟨g, hg⟩ ∈ κ.range →
      g ∈ S := fun g hg h => ⟨⟨g, hg⟩, h, rfl⟩
  have hSmem : ∀ g ∈ S, ∀ hg : g ∈ Subgroup.normalizer (L : Set G), act ⟨g, hg⟩ ∈ κ.range := by
    rintro _ ⟨n, hn, rfl⟩ hg
    exact hn
  have hLS : L ≤ S := fun l hl => hmemS l (Subgroup.le_normalizer hl)
    ⟨_, (hactL l hl (Subgroup.le_normalizer hl)).symm⟩
  have hES : E ≤ S := by
    rw [hEeq]
    exact sup_le (Subgroup.zpowers_le.mpr (hmemS c hcN ⟨1, by rw [map_one, hactc]⟩))
      (inf_le_right.trans hLS)
  have hPS : P ≤ S := sup_le hES (Subgroup.zpowers_le.mpr (hmemS x hx ⟨_, hactx.symm⟩))
  have hrange : ∀ g : P, act (Subgroup.inclusion hPN' g) ∈ κ.range := fun g =>
    hSmem g.1 (hPS g.2) _
  set ψ : P →* ProjGenLinGroup (Fin 3) K := (MonoidHom.ofInjective hκ).symm.toMonoidHom.comp
    ((act.comp (Subgroup.inclusion hPN')).codRestrict κ.range hrange) with hψdef
  have hψ : ∀ g : P, κ (ψ g) = act (Subgroup.inclusion hPN' g) := by
    intro g
    have h1 := MonoidHom.ofInjective_apply hκ (x := ψ g)
    rw [hψdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hψeq : ∀ (g : P) (w : ProjGenLinGroup (Fin 3) K),
      κ w = act (Subgroup.inclusion hPN' g) → ψ g = w := fun g w h =>
    hκ ((hψ g).trans h.symm)
  have hcP : c ∈ P := Subgroup.mem_sup_left hcE
  have hxP : x ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hψL : ∀ (g : P) (hgL : (g : G) ∈ L), ψ g =
      ((e (⟨g, hgL⟩ : L) : projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) :=
    fun g hgL => hψeq g _ (hactL g hgL (hPN' g.2)).symm
  have hψc : ψ ⟨c, hcP⟩ = 1 := hψeq _ 1 (by rw [map_one]; exact hactc.symm)
  have hψx : ψ ⟨x, hxP⟩ = ProjGenLinGroup.mk y := hψeq _ _ hactx.symm
  have hPLp : IsPGroup 3 ((P ⊓ L).subgroupOf L) :=
    (hPp.to_le (inf_le_left : P ⊓ L ≤ P)).comap_subtype
  have htrivL : ∀ g : P, ψ g = 1 → (g : G) ∈ L → g = 1 := by
    intro g h1 hgL
    rw [hψL g hgL] at h1
    have h2 : e (⟨g, hgL⟩ : L) = 1 := Subtype.ext h1
    have h3 : ((⟨g, hgL⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) = 1 :=
      e.injective (by rw [h2, map_one])
    have hmem : (⟨g, hgL⟩ : L) ∈ (P ⊓ L).subgroupOf L :=
      Subgroup.mem_subgroupOf.mpr (⟨g.2, hgL⟩ : (g : G) ∈ P ⊓ L)
    have h4 := injOn_mk_of_isPGroup Nat.prime_three hPLp hmem (Subgroup.one_mem _)
      (by rw [map_one]; exact h3)
    exact Subtype.ext (congrArg (fun z : L => (z : G)) h4)
  set BL : Subgroup P := (E ⊓ L).subgroupOf P with hBLdef
  have hBLP : E ⊓ L ≤ P := inf_le_left.trans le_sup_left
  have hBLp : IsPGroup 3 ((E ⊓ L).subgroupOf L) :=
    (IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num) :
      IsPGroup 3 (E ⊓ L : Subgroup G)).comap_subtype
  have hinjBL : Set.InjOn ψ BL := by
    intro g₁ hg₁ g₂ hg₂ h12
    have hg₁L : (g₁ : G) ∈ L := (Subgroup.mem_subgroupOf.mp hg₁).2
    have hg₂L : (g₂ : G) ∈ L := (Subgroup.mem_subgroupOf.mp hg₂).2
    rw [hψL g₁ hg₁L, hψL g₂ hg₂L] at h12
    have h1 := e.injective (Subtype.ext h12)
    have h2 := injOn_mk_of_isPGroup Nat.prime_three hBLp
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hg₁))
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hg₂)) h1
    have h3 : (g₁ : G) = g₂ := congrArg (fun z : L => (z : G)) h2
    exact Subtype.ext h3
  set H : Subgroup (ProjGenLinGroup (Fin 3) K) := BL.map ψ with hHdef
  have hH9 : Nat.card H = 9 := by
    rw [hHdef, Sec13.card_map_eq_of_injOn _ hinjBL, hBLdef, ← hB9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBLP).toEquiv
  set φ : P →* Subgroup.normalizer (L : Set G) ⧸ L.subgroupOf (Subgroup.normalizer (L : Set G)) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion hPN') with hφdef
  have hφ1 : ∀ g : P, φ g = 1 → (g : G) ∈ L := fun g h => by
    rw [hφdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact h
  have hφL : ∀ g : P, (g : G) ∈ L → φ g = 1 := fun g h => by
    rw [hφdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h
  have hpow : ∀ g : P, (g : G) ^ 3 = 1 → g ^ 3 = 1 := fun g h =>
    Subtype.ext (by rw [Subgroup.coe_pow, h, Subgroup.coe_one])
  set Q := Subgroup.zpowers (φ ⟨c, hcP⟩) ⊔ Subgroup.zpowers (φ ⟨x, hxP⟩) with hQdef
  have hQab : CFSG.Assembly.IsElemAbelian 3 Q :=
    Sec13.isElemAbelian_zpowers_sup (by rw [← map_pow, hpow _ hc3, map_one])
      (by rw [← map_pow, hpow _ hx3, map_one])
      (by rw [← map_mul, ← map_mul]; exact congrArg φ (Subtype.ext hxc.symm))
  have hφQ : ∀ g : P, φ g ∈ Q := by
    have hle : P ≤ (Q.comap φ).map P.subtype := by
      refine sup_le (hEeq.le.trans (sup_le ?_ ?_)) ?_
      · exact Subgroup.zpowers_le.mpr
          ⟨⟨c, hcP⟩, Subgroup.mem_sup_left (Subgroup.mem_zpowers _), rfl⟩
      · intro b hb
        refine ⟨⟨b, hBLP hb⟩, ?_, rfl⟩
        change φ ⟨b, hBLP hb⟩ ∈ Q
        rw [hφL _ hb.2]
        exact Q.one_mem
      · exact Subgroup.zpowers_le.mpr
          ⟨⟨x, hxP⟩, Subgroup.mem_sup_right (Subgroup.mem_zpowers _), rfl⟩
    intro g
    obtain ⟨g', hg', hgg'⟩ := hle g.2
    rw [show g = g' from Subtype.ext hgg'.symm]
    exact hg'
  have hcommQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    have := hQab.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : Q) ⟨b, hb⟩)
  have hψxH : ψ ⟨x, hxP⟩ ∉ H := by
    rintro ⟨l, hl, hlx⟩
    have hlE : (l : G) ∈ E := (Subgroup.mem_subgroupOf.mp hl).1
    have hlL : (l : G) ∈ L := (Subgroup.mem_subgroupOf.mp hl).2
    set k : P := ⟨x, hxP⟩ * l⁻¹ with hkdef
    have hk1 : ψ k = 1 := by rw [hkdef, map_mul, map_inv, ← hlx, mul_inv_cancel]
    have hkG : (k : G) = x * (l : G)⁻¹ := rfl
    have hk3 : (k : G) ^ 3 = 1 := by
      have h1 : k ^ 3 = 1 := htrivL _ (by rw [map_pow, hk1, one_pow])
        (hφ1 _ (by rw [map_pow, hkdef, map_mul, map_inv, hφL l hlL, inv_one, mul_one, ← map_pow,
          hpow _ hx3, map_one]))
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    have hkE : (k : G) ∉ E := by
      intro hk
      apply hxE
      have : x = (k : G) * l := by rw [hkG]; group
      rw [this]
      exact E.mul_mem hk hlE
    have hkc : (k : G) * c = c * k := by
      rw [hkG]
      have h1 := hEc c hcE l hlE
      calc x * (l : G)⁻¹ * c = x * ((l : G)⁻¹ * c) := by group
        _ = x * (c * (l : G)⁻¹) := by
            congr 1
            calc (l : G)⁻¹ * c = (l : G)⁻¹ * (c * l) * (l : G)⁻¹ := by group
              _ = (l : G)⁻¹ * (l * c) * (l : G)⁻¹ := by rw [h1]
              _ = c * (l : G)⁻¹ := by group
        _ = c * (x * (l : G)⁻¹) := by rw [← mul_assoc, hxc, mul_assoc]
    have hkm : ∀ m ∈ E ⊓ L, (k : G) * m = m * k := by
      intro m hm
      have hmP : m ∈ P := hBLP hm
      have hkN : (k : G) ∈ Subgroup.normalizer (L : Set G) := hPN' k.2
      have h1 : (k * ⟨m, hmP⟩ * k⁻¹ * (⟨m, hmP⟩ : P)⁻¹ : P) = 1 := by
        refine htrivL _ (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk1]; group) ?_
        change (k : G) * m * (k : G)⁻¹ * m⁻¹ ∈ L
        exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp hkN m).mp hm.2) (L.inv_mem hm.2)
      have h2 := congrArg Subtype.val h1
      change (k : G) * m * (k : G)⁻¹ * m⁻¹ = 1 at h2
      calc (k : G) * m = (k : G) * m * (k : G)⁻¹ * m⁻¹ * (m * k) := by group
        _ = m * k := by rw [h2, one_mul]
    have hEk : E ≤ Subgroup.centralizer ({(k : G)} : Set G) := by
      rw [hEeq]
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hkc.symm))
        fun m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hkm m hm).symm
    set W := E ⊔ Subgroup.zpowers (k : G) with hWdef
    have hWab : CFSG.Assembly.IsElemAbelian 3 W := by
      refine Sec13.isElemAbelian_sup hE (Sec13.isElemAbelian_zpowers hk3) fun a ha b hb => ?_
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hEk ha)
      exact (Commute.zpow_right (show Commute a (k : G) from h1) i).eq
    have hk1' : (k : G) ≠ 1 := fun h1 => hkE (h1 ▸ E.one_mem)
    have hko : orderOf (k : G) = 3 := orderOf_eq_prime hk3 hk1'
    have hcardk : Nat.card (Subgroup.zpowers (k : G)) = 3 := by rw [Nat.card_zpowers, hko]
    have hW81 : Nat.card W = 81 := by
      have hN : Subgroup.zpowers (k : G) ≤ Subgroup.normalizer (E : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _
          (Subgroup.mem_centralizer_iff.mpr fun a ha =>
            Subgroup.mem_centralizer_singleton_iff.mp (hEk ha)))
      have hcard := Sec6.card_sup_mul_card_inf hN
      have hinf : Subgroup.zpowers (k : G) ⊓ E = ⊥ := by
        have hdvd : Nat.card (Subgroup.zpowers (k : G) ⊓ E : Subgroup G) ∣ 3 := by
          have h1 := Subgroup.card_dvd_of_le
            (inf_le_left : Subgroup.zpowers (k : G) ⊓ E ≤ Subgroup.zpowers (k : G))
          rwa [hcardk] at h1
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact Subgroup.card_eq_one.mp h1
        · exfalso
          have heq : Subgroup.zpowers (k : G) ⊓ E = Subgroup.zpowers (k : G) :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcardk])
          have hkk : (k : G) ∈ Subgroup.zpowers (k : G) ⊓ E := by
            rw [heq]
            exact Subgroup.mem_zpowers _
          exact hkE hkk.2
      rw [hinf, Subgroup.card_bot, mul_one, hcardk, hE27, sup_comm] at hcard
      rw [hWdef]
      omega
    have hWP : W ≤ P := sup_le le_sup_left (Subgroup.zpowers_le.mpr k.2)
    exact hrank W hWP hWab hW81
  set R := ψ.range with hRdef
  have hRp : IsPGroup 3 R := by
    rintro ⟨_, g, rfl⟩
    obtain ⟨k, hk⟩ := hPp g
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← map_pow, hk, map_one, Subgroup.coe_one]
  have hHR : H ≤ R := by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨g, rfl⟩
  have hR27 : Nat.card R = 27 := by
    have h9 : 9 ∣ Nat.card R := hH9 ▸ Subgroup.card_dvd_of_le hHR
    have hle : Nat.card R ≤ 3 ^ 3 := by
      have := Item138Proof.card_le_of_isPGroup (le_top : R ≤ ⊤) hRp
      rwa [Subgroup.card_top, factorization_card_pgl_three_of_card_four hK4] at this
    have hne : Nat.card R ≠ 9 := by
      intro h
      apply hψxH
      rw [Subgroup.eq_of_le_of_card_ge hHR (by rw [h, hH9])]
      exact ⟨_, rfl⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hRp
    rw [hk] at h9 hle hne ⊢
    have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    have hk2 : 2 ≤ k := by
      by_contra hk2
      push Not at hk2
      interval_cases k <;> norm_num at h9
    interval_cases k
    · exact absurd rfl hne
    · rfl
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf 3 R (⊤ : Subgroup (ProjGenLinGroup (Fin 3) K)) :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top
      (by rw [hR27, Subgroup.card_top, factorization_card_pgl_three_of_card_four hK4]; norm_num)
  obtain ⟨n, -, hn⟩ := Sec18.exists_map_conj_eq_of_isSylowOf (isSylowOf_stdSylow hK hq hK4) hRsyl
  set T := (stdTorus K).map (MulAut.conj n).toMonoidHom with hTdef
  have hTR : T ≤ R := by
    rw [hn]
    exact Subgroup.map_mono le_sup_left
  have hT9 : Nat.card T = 9 := by
    rw [hTdef, Subgroup.card_map_of_injective (MulAut.conj n).injective, card_stdTorus hK hq]
  have hTab : CFSG.Assembly.IsElemAbelian 3 T :=
    Sec13.isElemAbelian_map isElemAbelian_stdTorus (MulAut.conj n).toMonoidHom
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    have := hTab.1
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : T) ⟨b, hb⟩)
  have hker3 : Nat.card ψ.ker = 3 := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, hP81] at h1
    change Nat.card ψ.ker * Nat.card R = 81 at h1
    rw [hR27] at h1
    omega
  have hker : ψ.ker = (Subgroup.zpowers c).subgroupOf P := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro g hg
      rw [Subgroup.mem_subgroupOf] at hg
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hg
      have : g = ⟨c, hcP⟩ ^ i := Subtype.ext (by simpa using hi.symm)
      rw [MonoidHom.mem_ker, this, map_zpow, hψc, one_zpow]
    · rw [hker3, ← card_zpowers_of_pow_three hc3 hc1]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.zpowers_le.mpr hcP)).toEquiv).ge
  have hdP : d ∈ P := Subgroup.mem_sup_left hdE
  have hPd : P ≤ Subgroup.centralizer ({d} : Set G) := by
    refine sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hEc d hdE a ha).symm)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hdx))
  have hψd : ψ ⟨d, hdP⟩ ∈ T := by
    by_contra hdT
    obtain ⟨τ, hτ, hτ1⟩ := Sec4.exists_tau hK hq
    apply not_comm_stdSylow hτ hτ1
    have hdc : ∀ r ∈ R, ψ ⟨d, hdP⟩ * r = r * ψ ⟨d, hdP⟩ := by
      rintro _ ⟨g, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hPd g.2)).symm
    have hd3 : ψ ⟨d, hdP⟩ ^ 3 = 1 := by
      rw [← map_pow, hpow _ (hE.2 d hdE), map_one]
    have hTd : CFSG.Assembly.IsElemAbelian 3 (T ⊔ Subgroup.zpowers (ψ ⟨d, hdP⟩)) := by
      refine Sec13.isElemAbelian_sup hTab (Sec13.isElemAbelian_zpowers hd3) fun a ha b hb => ?_
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact (Commute.zpow_right (show Commute a (ψ ⟨d, hdP⟩) from
        (hdc a (hTR ha)).symm) i).eq
    have hdR : ψ ⟨d, hdP⟩ ∈ R := ⟨_, rfl⟩
    have hTdR : T ⊔ Subgroup.zpowers (ψ ⟨d, hdP⟩) ≤ R :=
      sup_le hTR (Subgroup.zpowers_le.mpr hdR)
    have hTdeq : T ⊔ Subgroup.zpowers (ψ ⟨d, hdP⟩) = R := by
      refine Subgroup.eq_of_le_of_card_ge hTdR ?_
      have hlt : T < T ⊔ Subgroup.zpowers (ψ ⟨d, hdP⟩) :=
        lt_of_le_of_ne le_sup_left fun heq =>
          hdT (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      have h1 : Nat.card T < Nat.card (T ⊔ Subgroup.zpowers (ψ ⟨d, hdP⟩) : Subgroup _) :=
        Subgroup.card_lt_of_lt hlt
      have h2 : Nat.card (T ⊔ Subgroup.zpowers (ψ ⟨d, hdP⟩) : Subgroup _) ∣ 27 :=
        hR27 ▸ Subgroup.card_dvd_of_le hTdR
      have h3 : 9 ∣ Nat.card (T ⊔ Subgroup.zpowers (ψ ⟨d, hdP⟩) : Subgroup _) :=
        hT9 ▸ Subgroup.card_dvd_of_le (le_sup_left : T ≤ T ⊔ _)
      rw [hT9] at h1
      rw [hR27]
      obtain ⟨j, hj⟩ := h3
      have hj3 : j ∣ 3 := by
        obtain ⟨m, hm⟩ := h2
        rw [hj, mul_assoc] at hm
        exact ⟨m, Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 9) (by rw [← hm])⟩
      rcases (Nat.dvd_prime Nat.prime_three).mp hj3 with rfl | rfl <;> omega
    have hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
      have := hTd.1
      intro a ha b hb
      rw [← hTdeq] at ha hb
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : (T ⊔ Subgroup.zpowers _ : Subgroup _))
        ⟨b, hb⟩)
    intro a ha b hb
    have hna : n * a * n⁻¹ ∈ R := by rw [hn]; exact ⟨a, ha, rfl⟩
    have hnb : n * b * n⁻¹ ∈ R := by rw [hn]; exact ⟨b, hb, rfl⟩
    have h1 := hRab _ hna _ hnb
    calc a * b = n⁻¹ * ((n * a * n⁻¹) * (n * b * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * b * n⁻¹) * (n * a * n⁻¹)) * n := by rw [h1]
      _ = b * a := by group
  set F' : Subgroup P := T.comap ψ with hF'def
  set F : Subgroup G := F'.map P.subtype with hFdef
  have hF'T : F'.map ψ = T := by
    rw [hF'def, Subgroup.map_comap_eq, inf_eq_right.mpr hTR]
  have hkerF' : ψ.ker ≤ F' := fun g hg => by
    rw [MonoidHom.mem_ker] at hg
    change ψ g ∈ T
    rw [hg]
    exact T.one_mem
  have hF'27 : Nat.card F' = 27 := by
    have h1 := Step1914TriProof.card_map_mul_card_ker_subgroupOf ψ F'
    rw [hF'T, hT9] at h1
    have h2 : Nat.card (ψ.ker.subgroupOf F') = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerF').toEquiv, hker3]
    rw [h2] at h1
    omega
  have hF27 : Nat.card F = 27 := by
    rw [hFdef, Subgroup.card_map_of_injective P.subtype_injective, hF'27]
  have hFP : F ≤ P := Subgroup.map_subtype_le F'
  have hmemF : ∀ g : P, (g : G) ∈ F ↔ g ∈ F' := fun g => by
    constructor
    · rintro ⟨g', hg', hgg'⟩
      rwa [show g = g' from Subtype.ext hgg'.symm]
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hcF : c ∈ F := (hmemF ⟨c, hcP⟩).mpr (show ψ ⟨c, hcP⟩ ∈ T by rw [hψc]; exact T.one_mem)
  have hdF : d ∈ F := (hmemF ⟨d, hdP⟩).mpr hψd
  have htriv : ∀ g : P, ψ g = 1 → φ g = 1 → g = 1 := fun g h1 h2 => htrivL g h1 (hφ1 g h2)
  have hcommP : ∀ a b : P, ψ a ∈ T → ψ b ∈ T → a * b = b * a := by
    intro a b ha hb
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := htriv _
      (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommT _ ha _ hb]; group)
      (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommQ _ (hφQ a) _ (hφQ b)]; group)
    rw [← commutatorElement_def] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hFab : CFSG.Assembly.IsElemAbelian 3 F := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩
    · have h1 := congrArg Subtype.val (hcommP ⟨a, hFP a.2⟩ ⟨b, hFP b.2⟩ ((hmemF _).mp a.2)
        ((hmemF _).mp b.2))
      exact h1
    · have h1 : (⟨g, hFP hg⟩ : P) ^ 3 = 1 := htriv _
        (by rw [map_pow]; exact hTab.2 _ ((hmemF _).mp hg))
        (by rw [map_pow]; exact hQab.2 _ (hφQ _))
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hsec : Late.sectionCentralizer F L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf (hFP.trans hPN')]
    ext a
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    constructor
    · rintro ⟨haF, y, hy, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
      have h1 : act y = 1 := by
        rw [hactdef, MonoidHom.comp_apply, MonoidHom.comp_apply, hy, map_one]
      have h2 : ψ ⟨y, hFP haF⟩ = 1 := hκ (by rw [hψ, map_one]; exact h1)
      have h3 : (⟨y, hFP haF⟩ : P) ∈ ψ.ker := h2
      rw [hker] at h3
      exact h3
    · intro ha
      refine ⟨Subgroup.zpowers_le.mpr hcF ha, ?_⟩
      have hcT : c ∈ Sec4.thetaQuotCentralizer L :=
        ⟨⟨c, hcN⟩, by
          rw [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, hnc, map_one], rfl⟩
      exact Subgroup.zpowers_le.mpr hcT ha
  have hformula : ∀ (g : P) (z : L ⧸ aschbacherSolvableCore 3 L),
      ((e (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom (Subgroup.inclusion hPN' g)) z) :
        projImage (slPi true 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ψ g * (e z : ProjGenLinGroup (Fin 3) K) * (ψ g)⁻¹ := by
    intro g z
    rw [← hκapp, hψ g, hact, MulEquiv.symm_apply_apply]
  obtain ⟨n₀, hn₀⟩ := ProjGenLinGroup.mk_surjective n
  set D : Subgroup (GL (Fin 3) K) := (stdTypeC K).map (MulAut.conj n₀).toMonoidHom with hDdef
  have hDT : D.map ProjGenLinGroup.mk = T := by
    rw [hDdef, hTdef, stdTorus, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, hn₀]
  have hTC : Sec4.IsTypeCOn F L := by
    refine ⟨true, p, f, K, inferInstance, hK, hq, e, D,
      isTypeC_map_conj (Sec4.isTypeC_stdTypeC hK hq) (Sec4.mem_glPi_true _ n₀), ?_, ?_⟩
    · intro τ hτ
      obtain ⟨h, hN, hhF, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
      have hgT : ψ ⟨h, hFP hhF⟩ ∈ T := (hmemF ⟨h, hFP hhF⟩).mp hhF
      rw [← hDT] at hgT
      obtain ⟨y, hyD, hy⟩ := hgT
      exact ⟨y, hyD, fun z => by rw [hy]; exact hformula ⟨h, hFP hhF⟩ z⟩
    · intro y hyD
      have hyT : ProjGenLinGroup.mk y ∈ T := hDT ▸ ⟨y, hyD, rfl⟩
      rw [← hF'T] at hyT
      obtain ⟨g, hgF', hg⟩ := hyT
      refine ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨g, hPN' g.2, (hmemF g).mpr hgF', rfl⟩,
        fun z => ?_⟩
      rw [← hg]
      exact hformula g z
  exact ⟨F, hFP, hcF, hdF, hFab, hF27, hsec, hTC⟩

end CFSG.RankThree.PartTwo.Sec16.Proof1613Type
