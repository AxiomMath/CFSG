module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5r
public import CFSG.Quasithin.Vol2.Ch12Sec7L5s
public import CFSG.Quasithin.Vol2.Ch12Sec7L5t
public import CFSG.Quasithin.Vol2.Ch11C113b
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127
open scoped IsMulCommutative

namespace S127.L76

section H1

variable {Γ W : Type*} [Group Γ] [AddCommGroup W] [Module (ZMod 2) W]

theorem H1_subsingleton_of_central [Finite W] (ρ : Representation (ZMod 2) Γ W) {z : Γ}
    (hz : ∀ g : Γ, z * g = g * z) (hfix : ∀ w : W, ρ z w = w → w = 0) :
    Subsingleton (JonesParshall.H1 ρ) := by
  set ψ : W →ₗ[ZMod 2] W := ρ z - LinearMap.id with hψ
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    apply hfix
    have h0 : ρ z w - w = 0 := hw
    exact sub_eq_zero.mp h0
  have hsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hinj
  have hcomm : ∀ g : Γ, ∀ w : W, ψ (ρ g w) = ρ g (ψ w) := by
    intro g w
    simp only [hψ, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
    rw [← Module.End.mul_apply, ← map_mul, hz g, map_mul, Module.End.mul_apply]
  have hB : ∀ f ∈ JonesParshall.Z1 ρ, f ∈ JonesParshall.B1 ρ := by
    intro f hf
    obtain ⟨w₀, hw₀⟩ := hsurj (f z)
    refine ⟨w₀, funext fun g => ?_⟩
    show ρ g w₀ - w₀ = f g
    apply hinj
    have h1 := hf z g
    have h2 := hf g z
    rw [← hz g] at h2
    have h3 : ψ (f g) = ρ g (f z) - f z := by
      have e : ρ z (f g) - f g = ρ g (f z) - f z := by
        calc ρ z (f g) - f g = (f z + ρ z (f g)) - f z - f g := by abel
          _ = (f g + ρ g (f z)) - f z - f g := by rw [← h1, h2]
          _ = ρ g (f z) - f z := by abel
      simpa [hψ] using e
    rw [h3, map_sub, hcomm, hw₀]
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro f _
  exact hB f f.2

end H1

section Rep

variable {G : Type} [Group G] {V : Subgroup G} [IsMulCommutative ↥V]
  [Module (ZMod 2) (Additive ↥V)]

@[expose] noncomputable def linOf (a : MulAut ↥V) : Additive ↥V →ₗ[ZMod 2] Additive ↥V :=
  (MulEquiv.toAdditive a).toAddMonoidHom.toZModLinearMap 2

theorem linOf_apply (a : MulAut ↥V) (v : Additive ↥V) :
    linOf a v = Additive.ofMul (a (Additive.toMul v)) := rfl

@[expose] noncomputable def linHom : MulAut ↥V →* (Additive ↥V →ₗ[ZMod 2] Additive ↥V) where
  toFun := linOf
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

theorem linHom_apply (a : MulAut ↥V) (v : Additive ↥V) :
    linHom a v = Additive.ofMul (a (Additive.toMul v)) := rfl

end Rep

end S127.L76

open S127.L76 S127.L713 S127.L712 CFSG.LieType.BorelTits in
theorem lemma12_7_6_of
    (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp1271 G T L V → IsHatA6Block L →
      (pCoreOf 2 (L ⊔ T) = V ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
        V ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥) ∧
      (T ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
        pCoreOf 2 L = V ∧ pCoreOf 2 (Subgroup.normalizer (L : Set G)) = V ∧
          Subgroup.centralizer (V : Set G) = V ∧ Subgroup.normalizer (L : Set G) = L ⊔ T) := by
  intro G _ _ T L V h hblk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy := h.hyp
  obtain ⟨hcomm, hV64, hTV⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  have hT2 : IsPGroup 2 T := hy.sylow.1
  have hVT : V ≤ T := S127.L713.V_le_T h1222 h
  have hV2 : IsPGroup 2 V := hT2.to_le hVT
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer h
  have hTL := hy.normalizes
  obtain ⟨-, -, -, hX3, -, hXfix⟩ := setup1271_of h1222 G T L V h
  obtain ⟨x, hxX, hxC⟩ : ∃ x ∈ S127.XOf L, x ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hno
    have hbot : autOn (S127.XOf L) V = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨y, hyN, hyX, rfl⟩ := S127.Mod.mem_autOn'.1 ha
      rw [Subgroup.mem_bot]
      exact (S127.Mod.conjAct_eq_one' hyN).2 (by_contra fun hy' => hno ⟨y, hyX, hy'⟩)
    rw [hbot, Subgroup.card_bot] at hX3
    norm_num at hX3
  have hxL : x ∈ L := S127.L5.XOf_le L hxX
  have hVx : V ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := hXfix x hxX hxC
  have hVCL : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hVx]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxL))
  have hVL : V ≤ L := by
    have hc : ⁅V, L⁆ ≤ L := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have hvl : v * l * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL (hVT hv)) l).mp hl
      rw [commutatorElement_def]
      exact L.mul_mem hvl (L.inv_mem hl)
    calc V = ⁅V, L⁆ := hy.irrPlus.2.2.2.1.symm
      _ ≤ L := hc
  have hVO : V ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hVL hLV hV2
  have hUV : QuasithinUnique.blockU L = V := by
    have hle : V ≤ QuasithinUnique.blockU L := by
      show V ≤ ⁅QuasithinUnique.blockQ L, L⁆
      calc V = ⁅V, L⁆ := hy.irrPlus.2.2.2.1.symm
        _ ≤ ⁅pCoreOf 2 L, L⁆ := Subgroup.commutator_mono hVO le_rfl
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hblk.2.2.1, hV64])).symm
  let _ : Module (ZMod 2) (Additive ↥V) := AddCommMonoid.zmodModule (fun v => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact Subtype.ext (by simpa using S127.sq_eq_one_of_mem hy (Additive.toMul v).2))
  set φ : ↥L →* (Additive ↥V →ₗ[ZMod 2] Additive ↥V) :=
    linHom.comp ((conjAct V).comp (Subgroup.inclusion hLV)) with hφ
  have hφv : ∀ (ℓ : ↥L) (v : Additive ↥V),
      ((Additive.toMul (φ ℓ v) : ↥V) : G) =
        (ℓ : G) * ((Additive.toMul v : ↥V) : G) * (ℓ : G)⁻¹ := by
    intro ℓ v
    rw [hφ, MonoidHom.comp_apply, MonoidHom.comp_apply, linHom_apply, toMul_ofMul]
    exact S127.Mod.conjAct_val _ _
  have hφ1 : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro y hy'
    have hyQ : (y : G) ∈ pCoreOf 2 L := by
      rw [← ASInputs.C113.pCoreOf_subgroupOf] at hy'
      exact hy'
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hφv, Module.End.one_apply]
    have hvU : ((Additive.toMul v : ↥V) : G) ∈ QuasithinUnique.blockU L :=
      hUV ▸ (Additive.toMul v).2
    have hc := Subgroup.mem_centralizer_iff.mp (hblk.1.2.2.1.1 hvU).2 _ hyQ
    rw [hc, mul_inv_cancel_right]
  set ρ : Representation (ZMod 2) (↥L ⧸ CFSG.pCore 2 ↥L) (Additive ↥V) :=
    QuotientGroup.lift (CFSG.pCore 2 ↥L) φ hφ1 with hρ
  have hρmk : ∀ (ℓ : ↥L) (v : Additive ↥V),
      ρ (QuotientGroup.mk ℓ : ↥L ⧸ CFSG.pCore 2 ↥L) v = φ ℓ v := by
    intro ℓ v
    rw [hρ, QuotientGroup.lift_mk]
  set β : ↥(QuasithinUnique.blockU L) →* Multiplicative (Additive ↥V) :=
    { toFun := fun u => Multiplicative.ofAdd (Additive.ofMul (Subgroup.inclusion hUV.le u))
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hβ
  have hβs : Function.Surjective β := by
    intro w
    refine ⟨⟨((Additive.toMul (Multiplicative.toAdd w) : ↥V) : G),
      hUV.ge (Additive.toMul (Multiplicative.toAdd w)).2⟩, ?_⟩
    rfl
  have hβk : β.ker = (QuasithinUnique.blockZ L).subgroupOf (QuasithinUnique.blockU L) := by
    have hZ : QuasithinUnique.blockZ L = ⊥ := by
      rw [QuasithinUnique.blockZ, hUV, hVCL]
    rw [hZ, Subgroup.bot_subgroupOf, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker] at hu
    rw [Subgroup.mem_bot]
    have hu' : ((u : G)) = 1 := congrArg (fun w : Multiplicative (Additive ↥V) =>
      ((Additive.toMul (Multiplicative.toAdd w) : ↥V) : G)) hu
    exact Subtype.ext hu'
  have hβa : ∀ (ℓ : ↥L) (u v : ↥(QuasithinUnique.blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        ρ (QuotientGroup.mk ℓ : ↥L ⧸ CFSG.pCore 2 ↥L) (Multiplicative.toAdd (β u)) := by
    intro ℓ u v huv
    rw [hρmk]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hφv]
    exact huv
  have hxZ : (QuotientGroup.mk ⟨x, hxL⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have hxO : x ∈ oTwoZIn L := oTwoUpper_le _ hxX
    obtain ⟨y, hyc, hyx⟩ := Subgroup.mem_map.mp hxO
    have hyx' : y = ⟨x, hxL⟩ := Subtype.ext hyx
    rw [← hyx']
    exact hyc
  have hzfix : ∀ w : Additive ↥V,
      ρ (QuotientGroup.mk ⟨x, hxL⟩ : ↥L ⧸ CFSG.pCore 2 ↥L) w = w → w = 0 := by
    intro w hw
    rw [hρmk] at hw
    have hw' : x * ((Additive.toMul w : ↥V) : G) * x⁻¹ = ((Additive.toMul w : ↥V) : G) := by
      have := congrArg (fun u : Additive ↥V => ((Additive.toMul u : ↥V) : G)) hw
      rwa [hφv] at this
    have hmem : ((Additive.toMul w : ↥V) : G) ∈ V ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine ⟨(Additive.toMul w).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc ((Additive.toMul w : ↥V) : G) * x
          = (x * ((Additive.toMul w : ↥V) : G) * x⁻¹) * x := by rw [hw']
        _ = x * ((Additive.toMul w : ↥V) : G) := by group
    rw [hVx, Subgroup.mem_bot] at hmem
    have h1 : Additive.toMul w = 1 := Subtype.ext hmem
    rw [← ofMul_toMul w, h1, ofMul_one]
  have : Finite (Additive ↥V) := inferInstanceAs (Finite ↥V)
  have hH1 : Module.finrank (ZMod 2) (JonesParshall.H1 ρ) = 0 := by
    have := H1_subsingleton_of_central ρ (z := QuotientGroup.mk ⟨x, hxL⟩)
      (fun g => (Subgroup.mem_center_iff.mp hxZ g).symm) hzfix
    exact Module.finrank_zero_of_subsingleton
  have hsylLT : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_le hy.sylow le_sup_right
  have hrel := ASInputs.C113.relIndex_le_two_pow_finrank_H1 hsylLT hTL hblk.1 (Additive ↥V) ρ β
    hβs hβk hβa
  rw [hH1, pow_zero, hUV] at hrel
  set C : Subgroup G := T ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hQle : pCoreOf 2 (L ⊔ T) ≤ V ⊔ C := by
    rw [← Subgroup.relIndex_eq_one]
    have hne : (V ⊔ C).relIndex (pCoreOf 2 (L ⊔ T)) ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    exact le_antisymm hrel (Nat.one_le_iff_ne_zero.mpr hne)
  have hVQ : V ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right) (sup_le hLV hTV) hV2
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := by
    refine le_normalizer_of_conj_mem fun l hl c hc => ?_
    have e : l * c * l⁻¹ = c := by
      rw [Subgroup.mem_centralizer_iff.mp hc.2 l hl, mul_inv_cancel_right]
    rw [e]
    exact hc
  have hCQ : C ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
      (sup_le hLC (le_normalizer_inf_centralizer hTL)) (hT2.to_le inf_le_left)
  have hQ : pCoreOf 2 (L ⊔ T) = V ⊔ C := le_antisymm hQle (sup_le hVQ hCQ)
  have hVC : V ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← hVCL]
    exact inf_le_inf_left _ inf_le_right
  refine ⟨⟨hQ, hVC⟩, fun hC1 => ?_⟩
  rw [hC1, sup_bot_eq] at hQ
  have hOL : pCoreOf 2 L = V := by
    refine le_antisymm ?_ hVO
    rw [← hQ]
    exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 L) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
      (pCoreOf_isPGroup 2 L)
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    rw [← hOL]
    exact normalizer_le_normalizer_pCoreOf 2 L
  have hsylM : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (L : Set G)) :=
    isSylowTwoOf_of_le hy.sylow hTL
  have hOM : pCoreOf 2 (Subgroup.normalizer (L : Set G)) = V := by
    refine le_antisymm ?_ ?_
    · rw [← hQ]
      exact le_pCoreOf_of_le_normalizer 2
        ((pCoreOf_two_le_of_isSylowTwoOf hsylM).trans le_sup_right)
        ((sup_le Subgroup.le_normalizer hTL).trans (le_normalizer_pCoreOf 2 _))
        (pCoreOf_isPGroup 2 _)
    · exact le_pCoreOf_of_le_normalizer 2 (hVL.trans Subgroup.le_normalizer) hMV hV2
  have hNV := Lem20.normalizer_le_of_hyp1223 h1226 hy
  have hchar : QuasithinUnique.CharTwo (Subgroup.normalizer (L : Set G)) :=
    charTwo_of_inH hy.qtke.2.1 (hy.sylow.1.toSylow hy.sylow.2)
      ⟨hTL, by rw [hOM]; exact fun hb => hy.irrPlus.2.1 hb⟩
  have hCV : Subgroup.centralizer (V : Set G) = V := by
    refine le_antisymm (fun c hc => ?_) (fun v hv => ?_)
    · have hcM : c ∈ Subgroup.normalizer (L : Set G) :=
        hNV (Subgroup.centralizer_le_normalizer (V : Set G) hc)
      have := hchar (Subgroup.mem_inf.mpr ⟨hcM, by rw [hOM]; exact hc⟩)
      rwa [hOM] at this
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact congrArg Subtype.val (hcomm.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)
  refine ⟨hOL, hOM, hCV, le_antisymm (fun m hm => ?_) (sup_le Subgroup.le_normalizer hTL)⟩
  have hmV := hMV hm
  have ha : conjAct V ⟨m, hmV⟩ ∈ hy.MVbar :=
    S127.Mod.conjAct_mem_autOn (Subgroup.mem_inf.mpr ⟨hm, hmV⟩) hmV
  have hLT : hy.MVbar ≤ autOn (L ⊔ T) V := by
    rcases S127.Mod.lemma12_7_2_one h1222 h with h1 | ⟨h1, -⟩
    · rw [h1]
      exact A4.autOn_mono le_sup_left
    · rw [h1]
      exact sup_le (A4.autOn_mono le_sup_left) (A4.autOn_mono le_sup_right)
  obtain ⟨y, hyN, hyLT, hyc⟩ := S127.Mod.mem_autOn'.1 (hLT ha)
  have hym : y⁻¹ * m ∈ Subgroup.centralizer (V : Set G) := by
    rw [← S127.Mod.conjAct_eq_one' ((Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).inv_mem hyN) hmV)]
    have e : conjAct V ⟨y⁻¹ * m, (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).inv_mem hyN) hmV⟩ =
        (conjAct V ⟨y, hyN⟩)⁻¹ * conjAct V ⟨m, hmV⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e, hyc, inv_mul_cancel]
  have hyL : y⁻¹ * m ∈ L ⊔ T := (le_sup_left : L ≤ L ⊔ T) (hVL (hCV ▸ hym))
  have e : m = y * (y⁻¹ * m) := by group
  rw [e]
  exact (L ⊔ T).mul_mem hyLT hyL

end CFSG.Quasithin.H13
