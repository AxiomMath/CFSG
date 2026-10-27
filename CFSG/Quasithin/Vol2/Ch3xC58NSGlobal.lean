module

public import CFSG.Quasithin.Vol2.Ch3xC58NSInputs
public import CFSG.Quasithin.Vol2.Ch3xC58NSA5Mate
public import CFSG.Quasithin.Background.C58Global
public import CFSG.Quasithin.Background.C58Blocks
public import CFSG.Quasithin.Vol2.Ch3xC58NSGamma

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.C5 CFSG.Quasithin.C58
  Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

namespace GammaSetupNS

variable {H T R K₁ : Subgroup G} {t x : G} (hs : GammaSetupNS H T R K₁ t x)
include hs

theorem isSylowTwoOf_Y [Finite G] :
    IsSylowTwoOf T (normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G)) := by
  have hT : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hs.sylow.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]; exact hs.sylow.2
  exact isSylowTwoOf_of_le hT hs.le_normalizer_T₁

theorem pCoreOf_le_normalizer [Finite G] : pCoreOf 2 H ≤ normalizer (K₁ : Set G) := by
  have hUK := blockU_le hs.cfg.short
  have key : ∀ q ∈ pCoreOf 2 H, ∀ k ∈ K₁, q * k * q⁻¹ ∈ K₁ := by
    intro q hq k hk
    have h1 := hs.cfg.QH q hq k⁻¹ (inv_mem hk)
    have e : q * k * q⁻¹ = k * (k⁻¹ * q * k⁻¹⁻¹ * q⁻¹) := by group
    rw [e]
    exact mul_mem hk (hUK h1)
  intro q hq
  exact B6.mem_normalizer_of_forall_mem (fun k hk => key q hq k hk)
    (fun k hk => by simpa using key q⁻¹ (inv_mem hq) k hk)

theorem charTwo_γ [Finite G] : CharTwo (K₁ ⊔ (T ⊓ normalizer (K₁ : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTsylH : IsSylowTwoOf T H :=
    ⟨hs.TH, hs.sylow.1, fun h => hs.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hs.TH))⟩
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hTsylH
  have hle : K₁ ⊔ (T ⊓ normalizer (K₁ : Set G)) ≤ H :=
    sup_le hs.cfg.le_H (inf_le_left.trans hs.TH)
  have hP : pCoreOf 2 H ≤ K₁ ⊔ (T ⊓ normalizer (K₁ : Set G)) :=
    (le_inf hQT hs.pCoreOf_le_normalizer).trans le_sup_right
  have hle' : pCoreOf 2 H ≤ pCoreOf 2 (K₁ ⊔ (T ⊓ normalizer (K₁ : Set G))) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP
      (hle.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  intro y hy
  have hyC : y ∈ centralizer (pCoreOf 2 H : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle') hy.2
  exact hle' (hs.charTwo ⟨hle hy.1, hyC⟩)

theorem not_inf_le_blockQ [Finite G] : ¬ (T ⊓ normalizer (K₁ : Set G)) ⊓ K₁ ≤ blockQ K₁ := by
  rcases hs.cfg.typ with ⟨n, hn, hlin⟩ | h5
  · intro h
    obtain ⟨-, hR2', -⟩ := C56.lin2_module_facts hs.cfg.short (by omega) hlin hs.syl₁
    have h1 : (blockQ K₁).relIndex ((T ⊓ normalizer (K₁ : Set G)) ⊓ K₁) = 1 :=
      Subgroup.relIndex_eq_one.mpr h
    rw [hR2'] at h1
    have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · intro h
    obtain ⟨α, hα, hαk, -⟩ := h5
    have hSyl := hs.syl₁
    have hK₀2 : IsPGroup 2 (((T ⊓ normalizer (K₁ : Set G)) ⊓ K₁).subgroupOf K₁) :=
      hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    let Pp : Sylow 2 ↥K₁ := hK₀2.toSylow hSyl.2.2
    have hcard := card_sylow_alternating_five (Pp.mapSurjective hα)
    have htriv : ((Pp.mapSurjective hα : Sylow 2 (alternatingGroup (Fin 5))) :
        Subgroup (alternatingGroup (Fin 5))) = ⊥ := by
      rw [Sylow.coe_mapSurjective, eq_bot_iff]
      rintro _ ⟨k, hk, rfl⟩
      rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, hαk]
      exact (AppC.mem_pCore_iff_mem_blockQ k).mpr (h (Subgroup.mem_subgroupOf.mp hk))
    rw [htriv, Subgroup.card_bot] at hcard
    norm_num at hcard

theorem isSylowTwoOf_γ [Finite G] :
    IsSylowTwoOf (T ⊓ normalizer (K₁ : Set G)) (K₁ ⊔ (T ⊓ normalizer (K₁ : Set G))) := by
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  refine ⟨le_sup_right, hs.sylow.1.to_le inf_le_left, ?_⟩
  have h1 := card_sup_mul_card_inf_of_le_normalizer (inf_le_right : T₁ ≤ normalizer (K₁ : Set G))
  rw [sup_comm] at h1
  have h2 := card_eq_card_mul_relIndex (le_sup_right : T₁ ≤ K₁ ⊔ T₁)
  have h3 := card_eq_card_mul_relIndex (inf_le_right : T₁ ⊓ K₁ ≤ K₁)
  have hpos1 : 0 < Nat.card T₁ := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥(T₁ ⊓ K₁) := Nat.card_pos
  have heq : T₁.relIndex (K₁ ⊔ T₁) = (T₁ ⊓ K₁).relIndex K₁ := by
    have h4 : Nat.card T₁ * Nat.card ↥(T₁ ⊓ K₁) * T₁.relIndex (K₁ ⊔ T₁) =
        Nat.card T₁ * Nat.card ↥(T₁ ⊓ K₁) * (T₁ ⊓ K₁).relIndex K₁ := by
      calc Nat.card T₁ * Nat.card ↥(T₁ ⊓ K₁) * T₁.relIndex (K₁ ⊔ T₁) =
            Nat.card ↥(K₁ ⊔ T₁) * Nat.card ↥(T₁ ⊓ K₁) := by rw [h2]; ring
        _ = Nat.card T₁ * Nat.card K₁ := h1
        _ = Nat.card T₁ * Nat.card ↥(T₁ ⊓ K₁) * (T₁ ⊓ K₁).relIndex K₁ := by rw [h3]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hpos1 hpos2) h4
  show ¬ 2 ∣ T₁.relIndex (K₁ ⊔ T₁)
  rw [heq]
  exact hs.syl₁.2.2

theorem minParabolic_γ [Finite G] {M : Subgroup G} (hmin : MinParabolic H T M) :
    MinParabolic (K₁ ⊔ (T ⊓ normalizer (K₁ : Set G))) (T ⊓ normalizer (K₁ : Set G))
      ((K₁ ⊔ (T ⊓ normalizer (K₁ : Set G))) ⊓ M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  set P := K₁ ⊔ T₁ with hP
  have hT2 : IsPGroup 2 T := hs.sylow.1
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le inf_le_left
  have hsylP : IsSylowTwoOf T₁ P := hs.isSylowTwoOf_γ
  obtain ⟨hMax, hTM, -⟩ := isUniqueMaxOver_iff.mp hmin.uniqueMax
  have hPH : P ≤ H := sup_le hs.cfg.le_H (inf_le_left.trans hs.TH)
  have hsylIn : IsSylowIn 2 T₁ P := hsylP
  have hnn : ¬ P ≤ normalizer (T₁ : Set G) := by
    intro h
    apply hs.not_inf_le_blockQ
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun k hk => mem_normalizer_inf (h ((le_sup_left : K₁ ≤ P) hk)) (Subgroup.le_normalizer hk))
      (hT₁2.to_le inf_le_left)
  have hKT : oTwoUpper H ⊔ T = H := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
    exact sup_twoResidual_eq hmin.isSylow
  have hPM : ¬ P ≤ M := by
    intro h
    have hKM : K₁ ≤ M := le_sup_left.trans h
    have hgen : ∀ g ∈ T, conjSubgroup K₁ g ≤ M := fun g hg => by
      have := conjSubgroup_mono hKM g
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hTM hg))] at this
    have hOM : oTwoUpper H ≤ M := hs.cfg.gen.trans (iSup₂_le hgen)
    have hHM : H ≤ M := by rw [← hKT]; exact sup_le hOM hTM
    exact (lt_iff_le_not_ge.mp hMax.1).2 hHM
  set K₂ := conjSubgroup K₁ t with hK₂
  have hT₁K₂ : T₁ ≤ normalizer (K₂ : Set G) := fun s hs' => by
    have hts : t * s * t⁻¹ ∈ T₁ := (mem_normalizer_iff.mp (hs.le_normalizer_T₁ hs.tT) s).mp hs'
    rw [← conjSubgroup_eq_iff_mem_normalizer, hK₂, conjSubgroup_conjSubgroup]
    have e : t * s = (t * s * t⁻¹) * t := by group
    rw [e, ← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr hts.2]
  have hK₁K₂ : K₁ ≤ normalizer (K₂ : Set G) :=
    le_normalizer_of_commute fun a ha b hb => hs.comm_K₂ a ha b hb
  have hPK₂ : P ≤ normalizer (K₂ : Set G) := sup_le hK₁K₂ hT₁K₂
  have hPK₂T : P ⊓ K₂ ≤ T₁ := by
    refine hsylP.le_of_normalizes inf_le_left
      (fun g hg => mem_normalizer_inf (Subgroup.le_normalizer hg) (hPK₂ hg)) ?_
    rintro ⟨g, hg⟩
    obtain ⟨a, ha⟩ := C1.exists_pow_mem_of_mem_sup hT₁2 (inf_le_right :
      T₁ ≤ normalizer (K₁ : Set G)) hg.1
    have h1 : g ^ 2 ^ a ∈ blockQ K₁ := hs.inf_K₂_le ⟨ha, pow_mem hg.2 _⟩
    obtain ⟨b, hb⟩ := (C1.blockQ_isPGroup K₁) ⟨g ^ 2 ^ a, h1⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : (g ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simpa [pow_add, pow_mul] using hb'
  have hmax : ∀ Y : Subgroup G, T₁ ≤ Y → Y < P → Y ≤ P ⊓ M := by
    intro Y hT₁Y hYP
    refine le_inf hYP.le ?_
    by_contra hYM
    apply (lt_iff_le_not_ge.mp hYP).2
    refine sup_le ?_ hT₁Y
    have htt : t * t ∈ Y := hT₁Y (hs.sq_mem_T₁ hs.tT)
    have hYtt : conjSubgroup Y (t * t) = Y :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer htt)
    have htΞ : t ∈ normalizer ((Y ⊔ conjSubgroup Y t : Subgroup G) : Set G) := by
      rw [← conjSubgroup_eq_iff_mem_normalizer, conjSubgroup_sup, conjSubgroup_conjSubgroup, hYtt,
        sup_comm]
    have hYH : Y ≤ H := hYP.le.trans hPH
    have hYtH : conjSubgroup Y t ≤ H := by
      have := conjSubgroup_mono hYH t
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer (hs.TH hs.tT))] at this
    have hΞH : (Y ⊔ conjSubgroup Y t) ⊔ zpowers t = H := by
      refine hmin.eq_of_not_le ?_ ?_ ?_
      · exact hs.le_sup_zpowers.trans (sup_le_sup_right (hT₁Y.trans le_sup_left) _)
      · exact sup_le (sup_le hYH hYtH) (zpowers_le.mpr (hs.TH hs.tT))
      · intro h; exact hYM (le_sup_left.trans (le_sup_left.trans h))
    have hKΞ : K₁ ≤ Y ⊔ conjSubgroup Y t := by
      have hK := C1Pack.isShort2_eq_oTwoUpper hs.cfg.short
      rw [hK]
      refine oTwoUpper_le_of_pow_mem fun k hk => ?_
      have hkH : k ∈ (Y ⊔ conjSubgroup Y t) ⊔ zpowers t := by
        rw [hΞH]; exact hs.cfg.le_H hk
      exact C1.exists_pow_mem_of_mem_sup (hT2.to_le (zpowers_le.mpr hs.tT))
        (zpowers_le.mpr htΞ) hkH
    have hYK₂ : Y ≤ normalizer (K₂ : Set G) := hYP.le.trans hPK₂
    have hYt : conjSubgroup Y t ≤ Y ⊔ K₂ := by
      have h1 := conjSubgroup_mono hYP.le t
      rw [hP, conjSubgroup_sup,
        conjSubgroup_eq_iff_mem_normalizer.mpr (hs.le_normalizer_T₁ hs.tT)] at h1
      exact h1.trans (sup_le le_sup_right (hT₁Y.trans le_sup_left))
    intro k hk
    obtain ⟨y, hy, k₂, hk₂, hyk⟩ :=
      mem_sup_of_le_normalizer hYK₂ ((sup_le le_sup_left hYt) (hKΞ hk))
    have hk₂P : k₂ ∈ P := by
      have e : k₂ = y⁻¹ * k := by rw [hyk]; group
      rw [e]
      exact mul_mem (inv_mem (hYP.le hy)) ((le_sup_left : K₁ ≤ P) hk)
    rw [hyk]
    exact mul_mem hy (hT₁Y (hPK₂T ⟨hk₂P, hk₂⟩))
  have hlt : P ⊓ M < P := lt_of_le_of_ne inf_le_left fun h => hPM (h ▸ inf_le_right)
  exact minParabolic_of_select hsylIn hnn ⟨hlt, le_inf le_sup_right (inf_le_left.trans hTM), hmax⟩

theorem false_of_embed [Finite G] (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : quasithinIsQTKECat G) (hEmb : EmbedLocal)
    {M : Subgroup G} (hmin : MinParabolic H T M)
    (hUB : blockU K₁ ≤ baum (T ⊓ normalizer (K₁ : Set G)))
    (hQD : ∀ v ∈ baum (T ⊓ normalizer (K₁ : Set G)) ⊓ centralizer (blockU K₁ : Set G),
      ∃ u ∈ blockU K₁, ∃ d ∈ centralizer (K₁ : Set G), v = u * d)
    (hodd : ∀ y ∈ normalizer ((T ⊓ normalizer (K₁ : Set G) : Subgroup G) : Set G),
      Odd (orderOf y) → conjSubgroup (blockU K₁) y ≤ centralizer (blockU K₁ : Set G))
    (hWe : ∃ e ∈ blockU K₁, e ∈ conjSubgroup (blockU K₁) x ∧ e ∉ blockZ K₁ ∧
      ∀ y ∈ T ⊓ normalizer (K₁ : Set G), y * e = e * y) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUK := blockU_le hs.cfg.short
  set U₁ := blockU K₁ with hU₁
  set T₁ := T ⊓ normalizer (K₁ : Set G) with hT₁
  set Y := normalizer (T₁ : Set G) with hY
  have hT2 : IsPGroup 2 T := hs.sylow.1
  have hT₁2 : IsPGroup 2 T₁ := hT2.to_le inf_le_left
  have hTY : IsSylowTwoOf T Y := hs.isSylowTwoOf_Y
  have hidx₁ : T₁.relIndex T = 2 := hs.relIndex_T₁
  have hT₁T : T₁ ≤ T := inf_le_left
  have hT₁Y : T₁ ≤ Y := Subgroup.le_normalizer
  have htY : t ∈ Y := hs.le_normalizer_T₁ hs.tT
  have hxY : x ∈ Y := hs.xN
  have htT₁ : t ∉ T₁ := fun h => hs.tK h.2
  have hUT₁ : U₁ ≤ T₁ := hs.U_le_T₁
  have hT₁U : T₁ ≤ normalizer (U₁ : Set G) := T₁_le_normalizer_U
  obtain ⟨N₁, hN₁Y, -, hT₁N₁, hidxN₁, hsylN₁⟩ := exists_index_two hTY hT₁T hidx₁ le_rfl
  have hN₁T₁ : N₁ ≤ normalizer (T₁ : Set G) := hN₁Y
  have hN₁c : ∀ g ∈ N₁, conjSubgroup U₁ g ≤ centralizer (U₁ : Set G) := by
    intro g hg
    obtain ⟨a, haT₁, b, hbN₁, hbodd, rfl⟩ := exists_mul_odd hsylN₁ hN₁T₁ hg
    rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.mpr (hT₁U haT₁)]
    exact hodd b (hN₁Y hbN₁) hbodd
  have hxN₁ : x ∉ N₁ := fun h => hs.xU (hN₁c x h)
  have htN₁ : t ∉ N₁ := by
    intro htN
    have h1 : zpowers t ≤ T₁ :=
      le_of_isPGroup_of_normal hsylN₁ hN₁T₁ (zpowers_le.mpr htN)
        (hT2.to_le (zpowers_le.mpr hs.tT))
    exact htT₁ (h1 (mem_zpowers t))
  have hidxY : (N₁.subgroupOf Y).index = 2 := hidxN₁
  have hmulN₁ : ∀ a ∈ Y, ∀ b ∈ Y, (a * b ∈ N₁ ↔ (a ∈ N₁ ↔ b ∈ N₁)) := by
    intro a ha b hb
    have := Subgroup.mul_mem_iff_of_index_two hidxY (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa [mem_subgroupOf] using this
  have hxtN₁ : x * t ∈ N₁ := (hmulN₁ x hxY t htY).mpr (iff_of_false hxN₁ htN₁)
  set B := baum T₁ with hB
  have hYB : Y ≤ normalizer (B : Set G) := normalizer_le_normalizer_baum T₁
  set V := conjClosure U₁ N₁ with hV
  have hUV : U₁ ≤ V := le_conjClosure U₁ N₁
  have hN₁V : N₁ ≤ normalizer (V : Set G) := le_normalizer_conjClosure U₁ N₁
  have hconjV : ∀ g ∈ N₁, conjSubgroup U₁ g ≤ V := by
    intro g hg v hv
    rw [mem_conjSubgroup_iff] at hv
    have := mem_conjClosure (inv_mem hg) hv
    simpa [mul_assoc] using this
  have hVQ : V ≤ B ⊓ centralizer (U₁ : Set G) := by
    refine conjClosure_le fun n hn u hu => ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.mp (hYB (hN₁Y hn)) u).mp (hUB hu)
    · have h1 := hN₁c n⁻¹ (inv_mem hn)
      exact h1 (mem_conjSubgroup_iff.mpr (by simpa [mul_assoc] using hu))
  have hVT₁ : V ≤ T₁ := hVQ.trans (inf_le_left.trans inf_le_left)
  have hVC : V ≤ centralizer (U₁ : Set G) := hVQ.trans inf_le_right
  have hVV : V ≤ centralizer (V : Set G) := by
    have hgen : ∀ n ∈ N₁, V ≤ centralizer ((conjSubgroup U₁ n : Subgroup G) : Set G) := by
      intro n hn
      have h1 := (DoubleA3.le_centralizer_iff_conj n).mp hVC
      rwa [conjSubgroup_eq_iff_mem_normalizer.mpr (hN₁V hn)] at h1
    intro v hv
    show v ∈ centralizer ((Subgroup.closure {x | ∃ h ∈ N₁, ∃ z ∈ U₁, h * z * h⁻¹ = x} :
      Subgroup G) : Set G)
    rw [Subgroup.centralizer_closure, mem_centralizer_iff]
    rintro _ ⟨n, hn, u, hu, rfl⟩
    have h1 := hgen n⁻¹ (inv_mem hn) hv
    rw [mem_centralizer_iff] at h1
    exact h1 _ (mem_conjSubgroup_iff.mpr (by simpa [mul_assoc] using hu))
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    ((mem_centralizer_iff.mp (hVV hb)) a ha)
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨n, -, u, hu, rfl⟩ := hy
      have h1 := C1.blockU_sq hs.cfg.short u hu
      have : (n * u * n⁻¹) ^ 2 = n * u ^ 2 * n⁻¹ := by simp only [pow_two]; group
      rw [this, h1]; simp
    | one => simp
    | mul a b ha hb iha ihb =>
      have hab := hVcomm a ha b hb
      have : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
        simp only [pow_two]
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = a * a * (b * b) := by group
      rw [this, iha, ihb, one_mul]
    | inv a ha iha =>
      rw [inv_pow, iha, inv_one]
  have hVe : IsElemAbelian 2 V := isElemAbelian_two_iff.mpr ⟨hVcomm, hVsq⟩
  have hV2 : IsPGroup 2 V := hT₁2.to_le hVT₁
  have hKV : K₁ ≤ normalizer (V : Set G) := by
    have key : ∀ k ∈ K₁, ∀ v ∈ V, k * v * k⁻¹ ∈ V := by
      intro k hk v hv
      obtain ⟨u, hu, d, hd, rfl⟩ := hQD v (hVQ hv)
      have hdk : k * d = d * k := (mem_centralizer_iff.mp hd) k hk
      have hku : k * u * k⁻¹ ∈ U₁ :=
        (mem_normalizer_iff.mp (C1.le_normalizer_blockU K₁ hk) u).mp hu
      have hkd : k * d * k⁻¹ = d := by rw [hdk]; group
      have e : k * (u * d) * k⁻¹ = (k * u * k⁻¹ * u⁻¹) * (u * d) := by
        calc k * (u * d) * k⁻¹ = (k * u * k⁻¹) * (k * d * k⁻¹) := by group
          _ = (k * u * k⁻¹) * d := by rw [hkd]
          _ = (k * u * k⁻¹ * u⁻¹) * (u * d) := by group
      rw [e]
      exact mul_mem (hUV (mul_mem hku (inv_mem hu))) hv
    intro k hk
    exact B6.mem_normalizer_of_forall_mem (fun v hv => key k hk v hv)
      (fun v hv => by simpa using key k⁻¹ (inv_mem hk) v hv)
  set X := N₁ ⊔ K₁ with hX
  have hXV : X ≤ normalizer (V : Set G) := sup_le hN₁V hKV
  have hN₁X : N₁ ≤ X := le_sup_left
  have hKX : K₁ ≤ X := le_sup_right
  have hT₁X : T₁ ≤ X := hT₁N₁.trans hN₁X
  have hT₁N : T₁ ≤ normalizer (V : Set G) := hT₁N₁.trans hN₁V
  obtain ⟨e, heU, heUx, heZ, heT₁⟩ := hWe
  obtain ⟨hzZ, hz1⟩ := hs.z_mem heU heZ heT₁
  have hzV : e * (t⁻¹ * e * t) ∈ V := by
    refine mul_mem (hUV heU) (hconjV _ hxtN₁ ?_)
    rw [mem_conjSubgroup_iff] at heUx ⊢
    have : x * t * (t⁻¹ * e * t) * (x * t)⁻¹ = x * e * x⁻¹ := by group
    rw [this]; exact heUx
  have hTtop : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hT2, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]; exact hs.sylow.2
  have hVZ : V ⊓ (T ⊓ centralizer (T : Set G)) ≠ ⊥ := by
    intro h
    have hz : e * (t⁻¹ * e * t) ∈ V ⊓ (T ⊓ centralizer (T : Set G)) := by
      obtain ⟨h1, h2, -⟩ := mem_quasithinOmegaOneCenter_iff.mp hzZ
      exact ⟨hzV, h1, h2⟩
    rw [h] at hz
    exact hz1 hz
  have hNVc : CharTwo (normalizer (V : Set G)) :=
    CT.charTwo_normalizer_of_inf_center hs.even hTtop hV2 hVZ
  obtain ⟨S', hS', hT₁S'⟩ := A4.exists_isSylowTwoOf_ge (hT₁N₁.trans hN₁V) hT₁2
  have hS'card : Nat.card S' ≤ Nat.card T := by
    obtain ⟨P, hP'⟩ := hS'.2.1.exists_le_sylow
    have h1 : Nat.card S' ≤ Nat.card P := Subgroup.card_le_of_le hP'
    have h2 : Nat.card P = Nat.card (hT2.toSylow hs.sylow.2) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    exact h1.trans h2.le
  have hXc : CharTwo X := by
    refine charTwo_of_relIndex_le_two hNVc hS' hXV ?_
    have h1 : X.relIndex S' ∣ T₁.relIndex S' := Subgroup.relIndex_dvd_of_le_left S' hT₁X
    have h2 : T₁.relIndex S' ≤ 2 := by
      have e1 := card_eq_card_mul_relIndex hT₁S'
      have e2 := card_eq_card_mul_relIndex hT₁T
      rw [hidx₁] at e2
      have hpos : 0 < Nat.card T₁ := Nat.card_pos
      have : Nat.card T₁ * T₁.relIndex S' ≤ Nat.card T₁ * 2 := by
        rw [← e1, ← e2]; exact hS'card
      exact Nat.le_of_mul_le_mul_left this hpos
    have h0 : T₁.relIndex S' ≠ 0 := Subgroup.index_ne_zero_of_finite (H := T₁.subgroupOf S')
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h1).trans h2
  have hsylX : IsSylowTwoOf T₁ X := by
    obtain ⟨S'', hS'', hT₁S''⟩ := A4.exists_isSylowTwoOf_ge hT₁X hT₁2
    by_cases heq : T₁ = S''
    · rw [heq]; exact hS''
    exfalso
    have hlt : T₁.subgroupOf S'' < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => heq ?_
      exact le_antisymm hT₁S'' fun g hg => by
        have : (⟨g, hg⟩ : S'') ∈ T₁.subgroupOf S'' := htop ▸ trivial
        exact this
    have : Group.IsNilpotent S'' := hS''.2.1.isNilpotent
    have hlt' := Group.normalizerCondition_of_isNilpotent _ hlt
    obtain ⟨g, hgN, hgT⟩ := IsConcreteLE.exists_of_lt hlt'
    have hgY : (g : G) ∈ Y := by
      refine B6.mem_normalizer_of_forall_mem (fun a ha => ?_) (fun a ha => ?_)
      · have := (mem_normalizer_iff.mp hgN ⟨a, hT₁S'' ha⟩).mp (by simpa [mem_subgroupOf] using ha)
        simpa [mem_subgroupOf] using this
      · have := (mem_normalizer_iff.mp (inv_mem hgN) ⟨a, hT₁S'' ha⟩).mp
          (by simpa [mem_subgroupOf] using ha)
        simpa [mem_subgroupOf] using this
    have hgT₁ : (g : G) ∉ T₁ := fun h => hgT (by simpa [mem_subgroupOf] using h)
    have hgN₁ : (g : G) ∉ N₁ := by
      intro h
      have h1 : zpowers (g : G) ≤ T₁ :=
        le_of_isPGroup_of_normal hsylN₁ hN₁T₁ (zpowers_le.mpr h)
          (hS''.2.1.to_le (zpowers_le.mpr g.2))
      exact hgT₁ (h1 (mem_zpowers _))
    have hgN₁' : (g : G)⁻¹ ∉ N₁ := fun h => hgN₁ (by simpa using inv_mem h)
    have hxg : x * (g : G)⁻¹ ∈ N₁ :=
      (hmulN₁ x hxY _ (inv_mem hgY)).mpr (iff_of_false hxN₁ hgN₁')
    have hxX : x ∈ X := by
      have : x = (x * (g : G)⁻¹) * g := by group
      rw [this]
      exact mul_mem (hN₁X hxg) (hS''.1 g.2)
    apply hs.xU
    intro v hv
    rw [mem_conjSubgroup_iff] at hv
    have hv' : v ∈ V := by
      have := (mem_normalizer_iff.mp (hXV (inv_mem hxX)) _).mp (hUV hv)
      simpa [mul_assoc] using this
    rw [mem_centralizer_iff]
    intro u hu
    exact hVcomm u (hUV hu) v hv'
  have hNC : C5.NoCommonNormal T₁ (K₁ ⊔ T₁) Y := fun X' hX'R hX'1 hHX' hMX' =>
    hs.no_common_normal hX'R hX'1 hMX' (le_sup_left.trans hHX')
  have hconc := hEmb G hsimple hnonab hqtke T K₁ N₁ t x hs.sylow hs.cfg.short hs.cfg.typ hs.tT
    hs.tK hidx₁ hs.comm_K₂ hs.cfg.syl hs.charTwo_γ ⟨_, hs.minParabolic_γ hmin⟩ hNC hs.xN
    hs.xU hN₁T₁ hT₁N₁ hidxN₁ hsylN₁ hVe hVQ hXV hXc hsylX
  have hN₁U : N₁ ≤ normalizer (U₁ : Set G) := (le_inf hN₁X hN₁Y).trans hconc
  have hxt : x * t ∈ normalizer (U₁ : Set G) := hN₁U hxtN₁
  have hperm : ∀ a ∈ K₁, ∀ b ∈ conjSubgroup K₁ t⁻¹, a * b = b * a := by
    rcases hs.cfg.perm t⁻¹ (inv_mem hs.tT) with h | h
    · exact (hs.tK (by simpa using inv_mem (conjSubgroup_eq_iff_mem_normalizer.mp h))).elim
    · exact h
  apply hs.xU
  have e : conjSubgroup U₁ x = conjSubgroup U₁ t⁻¹ := by
    rw [show x = x * t * t⁻¹ by group, ← conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.mpr hxt]
  rw [e]
  intro v hv
  rw [mem_centralizer_iff]
  intro u hu
  exact hperm u (hUK hu) v (conjSubgroup_mono hUK t⁻¹ hv)

end GammaSetupNS

end CFSG.Quasithin.C58NS
