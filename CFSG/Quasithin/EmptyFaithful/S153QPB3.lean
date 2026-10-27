module

public import CFSG.Quasithin.EmptyFaithful.SBc17Out5V
public import CFSG.Quasithin.EmptyFaithful.S153QPB2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace SBc17

variable {G : Type} [Group G]

theorem mem_innerSub_of_autOn_conj {L V : Subgroup G}
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hD : L ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn L) {k : G}
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (hkV : k ∈ Subgroup.normalizer (V : Set G))
    (hS : ∃ g ∈ autOn L V, ∀ s ∈ autOn L V,
      conjAct V ⟨k, hkV⟩ * s * (conjAct V ⟨k, hkV⟩)⁻¹ = g * s * g⁻¹) : k ∈ innerSub L := by
  set S := autOn L V with hSdef
  set κ : MulAut ↥V := conjAct V ⟨k, hkV⟩ with hκ
  obtain ⟨g, hgS, hg⟩ := hS
  obtain ⟨x₀, hx₀N, hx₀L, hx₀⟩ := mem_autOn_iff.mp hgS
  set c : G := x₀⁻¹ * k with hc
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer hx₀L)) hk
  have hcV : c ∈ Subgroup.normalizer (V : Set G) := mul_mem (inv_mem hx₀N) hkV
  have hcomm : ∀ s ∈ S, conjAct V ⟨c, hcV⟩ * s = s * conjAct V ⟨c, hcV⟩ := by
    intro s hs
    have h1 : κ * s * κ⁻¹ = g * s * g⁻¹ := hg s hs
    have h3 : conjAct V ⟨c, hcV⟩ = g⁻¹ * κ := by
      have : (⟨c, hcV⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨x₀, hx₀N⟩⁻¹ * ⟨k, hkV⟩ := rfl
      rw [this, map_mul, map_inv, hx₀]
    rw [h3]
    calc g⁻¹ * κ * s = g⁻¹ * (κ * s * κ⁻¹) * κ := by group
      _ = g⁻¹ * (g * s * g⁻¹) * κ := by rw [h1]
      _ = s * (g⁻¹ * κ) := by group
  have hxc : ∀ x ∈ L, ⁅x, c⁆ ∈ oTwoZIn L := by
    intro x hx
    have hxN := hLV hx
    have hwN : ⁅x, c⁆ ∈ Subgroup.normalizer (V : Set G) := by
      simp only [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hxN hcV) (inv_mem hxN)) (inv_mem hcV)
    apply hD
    refine ⟨?_, ?_⟩
    · have h1 : c * x⁻¹ * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hcN x⁻¹).mp (inv_mem hx)
      have e : ⁅x, c⁆ = x * (c * x⁻¹ * c⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem hx h1
    · refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      have hcm := hcomm (conjAct V ⟨x, hxN⟩) (mem_autOn_iff.mpr ⟨x, hxN, hx, rfl⟩)
      have hw : conjAct V ⟨⁅x, c⁆, hwN⟩ = 1 := by
        have e : (⟨⁅x, c⁆, hwN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
            ⟨x, hxN⟩ * ⟨c, hcV⟩ * ⟨x, hxN⟩⁻¹ * ⟨c, hcV⟩⁻¹ := by
          apply Subtype.ext
          simp [commutatorElement_def]
        rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcm]
        group
      have h1 := congrArg (fun a : MulAut ↥V => ((a ⟨v, hv⟩ : ↥V) : G)) hw
      simp only [conjAct_coe, MulAut.one_apply] at h1
      calc v * ⁅x, c⁆ = (⁅x, c⁆ * v * ⁅x, c⁆⁻¹) * ⁅x, c⁆ := by rw [h1]
        _ = ⁅x, c⁆ * v := by group
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker = CFSG.pCore 2 ↥L :=
    QuotientGroup.ker_mk' _
  obtain ⟨ψ, hψ⟩ := exists_mulAut_comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    (QuotientGroup.mk'_surjective _) (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩)
    (map_normalizerMonoidHom_eq_one_iff hker hcN)
  have hcoe : ∀ x : ↥L, ((x * (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ x)⁻¹ : ↥L) : G) = ⁅(x : G), c⁆ := by
    intro x
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom, commutatorElement_def]
    group
  have hz : ∀ a : ↥L ⧸ CFSG.pCore 2 ↥L, a * (ψ a)⁻¹ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    intro a
    induction a using QuotientGroup.induction_on with | H x => ?_
    have h1 : ψ (QuotientGroup.mk x) = QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ x) :=
      hψ x
    rw [h1, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    obtain ⟨hmem, hcen⟩ := mem_oTwoZIn_iff.mp (hxc x x.2)
    convert hcen using 2
    apply Subtype.ext
    exact hcoe x
  have hψ1 := eq_of_forall_mul_inv_mem_center hq.1.commutator_eq_top ψ hz
  have hcM : c ∈ cMod L := by
    refine mem_cMod.mpr ⟨hcN, fun x hx => ?_⟩
    have h1 : ψ (QuotientGroup.mk (⟨x, hx⟩ : ↥L)) =
        QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ ⟨x, hx⟩) := hψ ⟨x, hx⟩
    rw [hψ1] at h1
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
        (⟨x, hx⟩ * (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ ⟨x, hx⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      show (QuotientGroup.mk (⟨x, hx⟩ : ↥L) : ↥L ⧸ CFSG.pCore 2 ↥L) *
        (QuotientGroup.mk (Subgroup.normalizerMonoidHom L ⟨c, hcN⟩ ⟨x, hx⟩))⁻¹ = 1
      rw [← h1, mul_inv_cancel]
    have h3 := (map_eq_one_iff_mem_pCoreOf hker _).mp h2
    rwa [hcoe] at h3
  exact mem_innerSub_iff.mpr ⟨x₀, hx₀L, c, hcM, by rw [hc]; group⟩

theorem conjAct_mem_autOn_of_conj {V W : Subgroup G} {b w : G}
    (hb : b ∈ Subgroup.normalizer (V : Set G)) (hw : w ∈ Subgroup.normalizer (V : Set G))
    (hbw : b * w * b⁻¹ ∈ W) :
    conjAct V ⟨b, hb⟩ * conjAct V ⟨w, hw⟩ * (conjAct V ⟨b, hb⟩)⁻¹ ∈ autOn W V := by
  have hbwV : b * w * b⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    mul_mem (mul_mem hb hw) (inv_mem hb)
  rw [conjAct_conj hb hw hbwV]
  exact mem_autOn_iff.mpr ⟨_, hbwV, hbw, rfl⟩

theorem conjAct_comm {V : Subgroup G} {k b : G} (hk : k ∈ Subgroup.normalizer (V : Set G))
    (hb : b ∈ Subgroup.normalizer (V : Set G)) :
    ∃ h : ⁅k, b⁆ ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨k, hk⟩ * conjAct V ⟨b, hb⟩ * (conjAct V ⟨k, hk⟩)⁻¹ * (conjAct V ⟨b, hb⟩)⁻¹ =
        conjAct V ⟨⁅k, b⁆, h⟩ := by
  have h : ⁅k, b⁆ ∈ Subgroup.normalizer (V : Set G) := by
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hk hb) (inv_mem hk)) (inv_mem hb)
  refine ⟨h, ?_⟩
  have e : (⟨⁅k, b⁆, h⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨k, hk⟩ * ⟨b, hb⟩ * ⟨k, hk⟩⁻¹ * ⟨b, hb⟩⁻¹ := by
    apply Subtype.ext
    simp [commutatorElement_def]
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]

end SBc17

end CFSG.Quasithin

namespace CFSG.Quasithin.SBc17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.QP
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_innerSub_of_autOn_sl3 {L V B W : Subgroup G} {k : G} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hD : L ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn L)
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (hkV : k ∈ Subgroup.normalizer (V : Set G))
    (hk5 : k ^ 5 = 1) (e : ↥(autOn L V) ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hmax : IsMaxParabolic2 (autOn L V) (autOn B V)) (hW : IsPGroup 2 ↥W)
    (hBW : ∀ b ∈ B, ∀ w ∈ W, b * w * b⁻¹ ∈ W) (hcomm : ∀ b ∈ B, ⁅b, k⁆ ∈ W) :
    k ∈ innerSub L := by
  classical
  set S := autOn L V with hSdef
  set κ : MulAut ↥V := conjAct V ⟨k, hkV⟩ with hκ
  have hSn : ∀ (y : G) (hyN : y ∈ Subgroup.normalizer (L : Set G))
      (hyV : y ∈ Subgroup.normalizer (V : Set G)), ∀ s ∈ S,
      conjAct V ⟨y, hyV⟩ * s * (conjAct V ⟨y, hyV⟩)⁻¹ ∈ S := by
    intro y hyN hyV s hs
    obtain ⟨x, hx, hxL, rfl⟩ := mem_autOn_iff.mp hs
    have hyx : y * x * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN x).mp hxL
    have hyxN : y * x * y⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      mul_mem (mul_mem hyV hx) (inv_mem hyV)
    rw [conjAct_conj hyV hx hyxN]
    exact mem_autOn_iff.mpr ⟨_, hyxN, hyx, rfl⟩
  have hκS : κ ∈ Subgroup.normalizer (S : Set (MulAut ↥V)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨fun hs => hSn k hk hkV s hs, fun hs => ?_⟩
    have h1 := hSn k⁻¹ (inv_mem hk) (inv_mem hkV) _ hs
    have h2 : conjAct V ⟨k⁻¹, inv_mem hkV⟩ = κ⁻¹ := by
      have : (⟨k⁻¹, inv_mem hkV⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨k, hkV⟩⁻¹ := rfl
      rw [this, map_inv]
    rw [h2] at h1
    simpa [mul_assoc] using h1
  set φ : MulAut ↥S := Subgroup.normalizerMonoidHom S ⟨κ, hκS⟩ with hφ
  have hφapp : ∀ s : ↥S, ((φ s : ↥S) : MulAut ↥V) = κ * s * κ⁻¹ := fun s =>
    Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨κ, hκS⟩ s
  have hφ5 : φ ^ 5 = 1 := by
    rw [hφ, ← map_pow]
    have h5 : (⟨κ, hκS⟩ : Subgroup.normalizer (S : Set (MulAut ↥V))) ^ 5 = 1 := by
      apply Subtype.ext
      show κ ^ 5 = 1
      rw [hκ, ← map_pow]
      have : (⟨k, hkV⟩ : Subgroup.normalizer (V : Set G)) ^ 5 = 1 := Subtype.ext hk5
      rw [this, map_one]
    rw [h5, map_one]
  set φ' : MulAut (Matrix.SpecialLinearGroup (Fin 3) F) := MulAut.congr e φ with hφ'
  have hφ'5 : φ' ^ 5 = 1 := by rw [hφ', ← map_pow, hφ5, map_one]
  have hφ'app : ∀ s : ↥S, φ' (e s) = e (φ s) := fun s => by
    rw [hφ', MulAut.congr_apply]
    simp [MulEquiv.trans_apply]
  have hP := isMaxParabolic2_top_of_mulEquiv hmax e
  set X : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    ((autOn W V).subgroupOf S).map e.toMonoidHom with hX
  set P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    ((autOn B V).subgroupOf S).map e.toMonoidHom with hP'
  have hX2 : IsPGroup 2 ↥X := by
    intro y
    obtain ⟨s, hs, hy⟩ := Subgroup.mem_map.mp y.2
    have hs' : (s : MulAut ↥V) ∈ autOn W V := hs
    obtain ⟨w, hwV, hwW, hws⟩ := mem_autOn_iff.mp hs'
    obtain ⟨m, hm⟩ := hW ⟨w, hwW⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    have h1 : (s ^ 2 ^ m : ↥S) = 1 := by
      apply Subtype.ext
      show ((s : ↥S) : MulAut ↥V) ^ 2 ^ m = 1
      rw [← hws, ← map_pow]
      have hwpow : w ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      have : (⟨w, hwV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ m = 1 := by
        apply Subtype.ext
        simpa using hwpow
      rw [this, map_one]
    show (y : Matrix.SpecialLinearGroup (Fin 3) F) ^ 2 ^ m = 1
    rw [← hy]
    show (e s) ^ 2 ^ m = 1
    rw [← map_pow, h1, map_one]
  have hPX : ∀ p ∈ P, ∀ x ∈ X, p * x * p⁻¹ ∈ X := by
    intro p hp x hx
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hp
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    have hs' : (s : MulAut ↥V) ∈ autOn B V := hs
    have ht' : (t : MulAut ↥V) ∈ autOn W V := ht
    obtain ⟨b, hbV, hbB, hbs⟩ := mem_autOn_iff.mp hs'
    obtain ⟨w, hwV, hwW, hwt⟩ := mem_autOn_iff.mp ht'
    refine ⟨s * t * s⁻¹, ?_, by simp⟩
    show ((s * t * s⁻¹ : ↥S) : MulAut ↥V) ∈ autOn W V
    have : ((s * t * s⁻¹ : ↥S) : MulAut ↥V) = (s : MulAut ↥V) * (t : MulAut ↥V) * (s : MulAut ↥V)⁻¹ := rfl
    rw [this, ← hbs, ← hwt]
    exact conjAct_mem_autOn_of_conj hbV hwV (hBW b hbB w hwW)
  have hφP : ∀ p ∈ P, φ' p * p⁻¹ ∈ X := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hp
    have hs' : (s : MulAut ↥V) ∈ autOn B V := hs
    obtain ⟨b, hbV, hbB, hbs⟩ := mem_autOn_iff.mp hs'
    refine ⟨φ s * s⁻¹, ?_, ?_⟩
    · show (((φ s * s⁻¹ : ↥S)) : MulAut ↥V) ∈ autOn W V
      have h1 : ((φ s * s⁻¹ : ↥S) : MulAut ↥V) =
          κ * (s : MulAut ↥V) * κ⁻¹ * (s : MulAut ↥V)⁻¹ := by
        rw [show ((φ s * s⁻¹ : ↥S) : MulAut ↥V) = ((φ s : ↥S) : MulAut ↥V) * (s : MulAut ↥V)⁻¹ from rfl,
          hφapp]
      rw [h1, ← hbs]
      obtain ⟨hc, hcc⟩ := conjAct_comm hkV hbV
      rw [hκ, hcc]
      refine mem_autOn_iff.mpr ⟨_, hc, ?_, rfl⟩
      have : ⁅k, b⁆ = (⁅b, k⁆)⁻¹ := (commutatorElement_inv b k).symm
      rw [this]
      exact inv_mem (hcomm b hbB)
    · show e (φ s * s⁻¹) = φ' (e s) * (e s)⁻¹
      rw [hφ'app, map_mul, map_inv]
  obtain ⟨g, hg⟩ := exists_conj_of_aut_trivial_mod_two_group φ' hφ'5 hP hX2 hPX hφP
  apply mem_innerSub_of_autOn_conj hLV hq hD hk hkV
  refine ⟨((e.symm g : ↥S) : MulAut ↥V), (e.symm g).2, fun s hs => ?_⟩
  have h1 := hg (e ⟨s, hs⟩)
  rw [hφ'app] at h1
  have h2 : φ ⟨s, hs⟩ = e.symm g * ⟨s, hs⟩ * (e.symm g)⁻¹ := by
    apply e.injective
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h3 := congrArg (fun t : ↥S => (t : MulAut ↥V)) h2
  simpa [hφapp] using h3

end CFSG.Quasithin.SBc17
