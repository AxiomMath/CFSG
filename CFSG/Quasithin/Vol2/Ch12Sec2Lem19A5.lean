module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem19Fin
public import CFSG.Quasithin.H13.A7KLocal
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem7One
public import CFSG.Quasithin.Background.I62Conj
public import CFSG.Quasithin.Vol2.Ch12Sec5L11
public import CFSG.Quasithin.Vol2.Ch12Sec2Cases

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem19S

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_comm {H W : Subgroup G} (hW : IsTwoReducedIn H W)
    (hO2 : pCoreOf 2 H ≤ Subgroup.centralizer (W : Set G))
    (hHC : ¬ H ≤ Subgroup.centralizer (W : Set G))
    (eK : ↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* alternatingGroup (Fin 5))
    {h : G} (hh : h ∈ H)
    (hk : ∀ k ∈ oTwoUpper H, h * k * h⁻¹ * k⁻¹ ∈ H ⊓ Subgroup.centralizer (W : Set G)) :
    h ∈ Subgroup.centralizer (W : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hHW, -, hD⟩ := hW
  set K := oTwoUpper H with hKdef
  set P := H ⊓ Subgroup.centralizer (W : Set G) with hPdef
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh, B6.le_normalizer_centralizer hHW hh⟩
  have hPconj : ∀ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ P := fun h hh x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHP hh) x).mp hx
  set α : ↥K →* alternatingGroup (Fin 5) := A7.kHom eK with hα
  have hαs : Function.Surjective α := A7.kHom_surjective eK
  have hαker : ∀ k : ↥K, α k = 1 ↔ k ∈ CFSG.pCore 2 ↥K := by
    intro k
    rw [← A7.kBar_eq_one_iff eK k]
    constructor
    · intro h1
      show ((α k : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = 1
      rw [h1]
      rfl
    · intro h1
      exact Subtype.ext h1
  have hO2K : ∀ k : ↥K, k ∈ CFSG.pCore 2 ↥K → (k : G) ∈ P := by
    intro k hk
    have h1 : (k : G) ∈ pCoreOf 2 K := by
      exact ⟨k, hk, rfl⟩
    have h2 : pCoreOf 2 K ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
        (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact ⟨hKH k.2, hO2 (h2 h1)⟩
  have hKP : ¬ K ≤ P := by
    intro hKP
    exact hHC (hD H le_rfl Subgroup.le_normalizer fun d hd => by
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H hd
      exact ⟨k, (hKP hk).2⟩)
  have hαP : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ P := by
    intro k
    refine ⟨fun h1 => hO2K k ((hαker k).mp h1), fun hk => ?_⟩
    have hPn : (P.subgroupOf K).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      push_cast
      exact hPconj g (hKH g.2) x hx⟩
    have hQn : ((P.subgroupOf K).map α).Normal := hPn.map α hαs
    rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin 5) (by simp)
        (N := (P.subgroupOf K).map α) with h | h
    · have : α k ∈ (P.subgroupOf K).map α := ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      apply hKP
      intro x hx
      have : α ⟨x, hx⟩ ∈ (P.subgroupOf K).map α := by rw [h]; trivial
      obtain ⟨y, hy, hyx⟩ := this
      have h2 : α (y⁻¹ * ⟨x, hx⟩) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
      have h3 := hO2K _ ((hαker _).mp h2)
      have h4 : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥K) : G) := by push_cast; group
      rw [h4]
      exact P.mul_mem (Subgroup.mem_subgroupOf.mp hy) h3
  have hconj : ∀ g ∈ H, ∀ d ∈ H, (∀ k ∈ K, d * k * d⁻¹ * k⁻¹ ∈ P) →
      ∀ k ∈ K, (g * d * g⁻¹) * k * (g * d * g⁻¹)⁻¹ * k⁻¹ ∈ P := by
    intro g hg d _ hd k hk
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hHK (H.inv_mem hg)) k).mp hk
      simpa using this
    have h1 := hPconj g hg _ (hd _ hk')
    convert h1 using 1
    group
  let D : Subgroup G :=
    { carrier := {h | h ∈ H ∧ ∀ k ∈ K, h * k * h⁻¹ * k⁻¹ ∈ P}
      one_mem' := ⟨H.one_mem, fun k _ => by simp [P.one_mem]⟩
      mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, fun k hk => by
        have e1 : a * b * k * (a * b)⁻¹ * k⁻¹ =
            a * (b * k * b⁻¹ * k⁻¹) * a⁻¹ * (a * k * a⁻¹ * k⁻¹) := by group
        rw [e1]
        exact P.mul_mem (hPconj a ha.1 _ (hb.2 k hk)) (ha.2 k hk)⟩
      inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, fun k hk => by
        have e1 : a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ = a⁻¹ * (a * k * a⁻¹ * k⁻¹)⁻¹ * a⁻¹⁻¹ := by group
        rw [e1]
        exact hPconj _ (H.inv_mem ha.1) _ (P.inv_mem (ha.2 k hk))⟩ }
  have hDH : D ≤ H := fun d hd => hd.1
  have hHD : H ≤ Subgroup.normalizer (D : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff.mpr fun d => ⟨fun hd => ?_, fun hd => ?_⟩
    · exact ⟨H.mul_mem (H.mul_mem hg hd.1) (H.inv_mem hg), hconj g hg d hd.1 hd.2⟩
    · have hd1 : d ∈ H := by
        have := H.mul_mem (H.mul_mem (H.inv_mem hg) hd.1) hg
        simpa [mul_assoc] using this
      have := hconj g⁻¹ (H.inv_mem hg) _ hd.1 hd.2
      refine ⟨hd1, ?_⟩
      simpa [mul_assoc] using this
  have hD2 : ∀ d ∈ D, ∃ a : ℕ, d ^ 2 ^ a ∈ Subgroup.centralizer (W : Set G) := by
    intro d hd
    obtain ⟨a, ha⟩ := exists_pow_mem_oTwoUpper H hd.1
    refine ⟨a, ?_⟩
    have hdD : d ^ 2 ^ a ∈ D := D.pow_mem hd _
    set x : ↥K := ⟨d ^ 2 ^ a, ha⟩ with hx
    have hxc : α x ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨k, rfl⟩ := hαs y
      have h1 : α (x * k * x⁻¹ * k⁻¹) = 1 := by
        rw [hαP]
        have := hdD.2 k k.2
        push_cast
        exact this
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at hxc
    exact ((hαP x).mp hxc).2
  exact hD D hDH hHD hD2 ⟨hh, hk⟩

theorem le_normalizer_of_isPGroup {V A : Subgroup G} (hVe : IsElemAbelian 2 V)
    (hAe : IsElemAbelian 2 A) (hcard : Nat.card V = Nat.card A) (hTIV : IsTISetIn V ⊤)
    (hTIA : IsTISetIn A ⊤) (hcross : ∀ g : G, V ≠ conjSubgroup A g → conjSubgroup A g ⊓ V = ⊥)
    (hU : ASInputs.tiU V A ≠ ⊥) (hP : IsPGroup 2 ↥(V ⊔ A)) :
    V ≤ Subgroup.normalizer (A : Set G) := by
  by_contra hVA
  have hlt : ASInputs.tiU V A < V :=
    lt_of_le_of_ne inf_le_left fun h => hVA (h ▸ inf_le_right)
  have h := I62.Hyp.mk' hVe hAe hcard hTIV hTIA hcross hU hlt
  have hN := h.le_normalizer_of_le (S := V ⊔ A) le_rfl hP le_sup_left
  have hB : ASInputs.tiB V A = A := inf_eq_left.mpr (le_sup_right.trans hN)
  have hc := h.card_tiU_eq
  rw [hB, ← hcard] at hc
  apply hVA
  have : ASInputs.tiU V A = V := Subgroup.eq_of_le_of_card_ge inf_le_left hc.ge
  exact this ▸ inf_le_right

omit [Finite G] in
theorem mem_normalizer_of_TI {V : Subgroup G}
    (hTI : ∀ g : G, CFSG.conjugate V g = V ∨ V ⊓ CFSG.conjugate V g = ⊥) {g x : G}
    (hx : x ∈ V) (hx1 : x ≠ 1) (hgx : g * x * g⁻¹ ∈ V) :
    g ∈ Subgroup.normalizer (V : Set G) := by
  rcases hTI g with h | h
  · refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    rw [← BlueprintB2.mem_conjugate_iff, h]
  · exfalso
    have : x ∈ V ⊓ CFSG.conjugate V g := ⟨hx, BlueprintB2.mem_conjugate_iff.mpr hgx⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx1 this

omit [Finite G] in
theorem isElemAbelian_conjugate {V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G) :
    IsElemAbelian 2 (CFSG.conjugate V g) := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have hx := BlueprintB2.mem_conjugate_iff.mp x.2
    have hy := BlueprintB2.mem_conjugate_iff.mp y.2
    have h := congrArg Subtype.val (hV.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at h ⊢
    calc (x : G) * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h]
      _ = y * x := by group
  · have h := hV.2 _ (BlueprintB2.mem_conjugate_iff.mp hx)
    rw [conj_pow, conj_eq_one_iff] at h
    exact h

theorem zmod_two_sum_eq_zero : ∀ p q r t : ZMod 2, p + -q = r + -t → t + r + q + p = 0 := by
  decide

omit [Finite G] in
theorem card_conjugate (V : Subgroup G) (g : G) : Nat.card (CFSG.conjugate V g) = Nat.card V :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem false_of_A5Sum {T L V H : Subgroup G}
    (hH : Hyp1223 G T L V) (hHs : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hTV : T ≤ Subgroup.normalizer (V : Set G)) (hV4 : ¬ Nat.card V ≤ 4)
    (hTI : ∀ g : G, CFSG.conjugate V g = V ∨ V ⊓ CFSG.conjugate V g = ⊥)
    (hVO : ¬ V ≤ pCoreOf 2 H)
    (hCT : T ⊓ Subgroup.centralizer (VZ T H : Set G) = pCoreOf 2 H)
    (hO2 : pCoreOf 2 H ≤ H ⊓ Subgroup.centralizer (VZ T H : Set G))
    (hker : H ⊓ Subgroup.centralizer (VZ T H : Set G) ≤
      kerIn (H ⊓ Subgroup.normalizer (V : Set G)) H)
    (hHC : ¬ H ≤ Subgroup.centralizer (VZ T H : Set G))
    (hLie : LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 2)
    (hA5 : IsA5ModuleSum (oTwoUpper H) ⁅VZ T H, oTwoUpper H⁆) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, rfl⟩ := exists_sylow_coe_eq hH.sylow
  set K := oTwoUpper H with hKdef
  set W := VZ (S : Subgroup G) H with hWdef
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set P := H ⊓ Subgroup.centralizer (W : Set G) with hPdef
  have hTH : (S : Subgroup G) ≤ H := hHs.1.1
  have hTM : (S : Subgroup G) ≤ M := hH.normalizes
  have hKH : K ≤ H := oTwoUpper_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_oTwoUpper H
  have hTK : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) := hTH.trans hHK
  have hWred : IsTwoReducedIn H W := Lem7.isTwoReducedIn_VZ hH hHs
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := hWred.2.1
  have hO2' : pCoreOf 2 H ≤ Subgroup.centralizer (W : Set G) := fun x hx => (hO2 hx).2
  have hWT : W ≤ (S : Subgroup G) :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWred.1 hWred.2.1
      (B2F.isPGroup_of_isElemAbelian hWred.2.2.1)).trans
    (A7.pCoreOf_le_of_le_normalizer S (hTH.trans Subgroup.le_normalizer))
  have hVe : IsElemAbelian 2 V := S125.isElemAbelian_of_hyp1223 hH
  have hVT : V ≤ (S : Subgroup G) := S125.le_of_hyp1223 hH
  have hVH : V ≤ H := hVT.trans hTH
  obtain ⟨eK⟩ : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) := by
    rcases hLie with ⟨-, -, F, _, _, hF, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
        (Or.inl (by rw [hF]; norm_num))
      exact ⟨e.trans e5⟩
    all_goals exact absurd h0 (by norm_num)
  have hO2KP : pCoreOf 2 K ≤ P := fun x hx =>
    ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH hx,
      hO2' (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKH)
        (hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hx)⟩
  have hkBar1 : ∀ x : ↥K, A7.kBar eK x = 1 → (x : G) ∈ P := by
    intro x hx
    rw [A7.kBar_eq_one_iff] at hx
    exact hO2KP ⟨x, hx, rfl⟩
  set φ : ↥H →* Equiv.Perm (Fin 5) := (A7.kAct eK).comp (Subgroup.inclusion hHK) with hφ
  have hφK : ∀ (k : G) (hk : k ∈ K), φ ⟨k, hKH hk⟩ = A7.kBar eK ⟨k, hk⟩ :=
    fun k hk => A7.kAct_of_mem eK hk
  have hφker : ∀ (h : G) (hh : h ∈ H), φ ⟨h, hh⟩ = 1 → h ∈ Subgroup.centralizer (W : Set G) :=
    fun h hh h1 => mem_centralizer_of_comm hWred hO2' hHC eK hh fun k hk =>
      hO2KP (A7.comm_mem_of_kAct_eq_one eK (hHK hh) h1 hk)
  obtain ⟨⟨k, hkK, hkN, hk3, hkO⟩, hnot⟩ := A7.exists_borel S hTK eK
  have hkM : k ∈ M := A7.normalizer_inf_le_of_hStar S hHs hKH hTK hnot ⟨hKH hkK, hkN⟩
  have hkH : k ∈ H := hKH hkK
  set c := A7.kBar eK ⟨k, hkK⟩ with hcdef
  have hc3 : c ^ 3 = 1 := by
    rw [hcdef, ← map_pow]
    have : (⟨k, hkK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
    rw [this, map_one]
  have hc1 : c ≠ 1 := by
    intro h
    rw [hcdef, A7.kBar_eq_one_iff] at h
    exact hkO ⟨_, h, rfl⟩
  set Sb : Subgroup (Equiv.Perm (Fin 5)) :=
    (((S : Subgroup G) ⊓ K).subgroupOf K).map (A7.kBar eK) with hSbdef
  have hSbA : Sb ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨t, -, rfl⟩
    exact A7.kBar_mem eK t
  have hSb4 : Nat.card Sb = 4 := by
    obtain ⟨hS2, hSodd⟩ := A7.sylow_inf_of_le_normalizer S hTK
    have hS1 : IsPGroup 2 ((((S : Subgroup G) ⊓ K)).subgroupOf K) :=
      hS2.comap_of_injective K.subtype K.subtype_injective
    set P1 : Sylow 2 ↥K := hS1.toSylow hSodd with hP1def
    have hP1 : (P1 : Subgroup ↥K) = ((S : Subgroup G) ⊓ K).subgroupOf K :=
      IsPGroup.toSylow_coe hS1 hSodd
    set P2 : Sylow 2 ↥(alternatingGroup (Fin 5)) := P1.mapSurjective (A7.kHom_surjective eK)
      with hP2def
    have hP2 : (P2 : Subgroup ↥(alternatingGroup (Fin 5))) =
        (((S : Subgroup G) ⊓ K).subgroupOf K).map (A7.kHom eK) := by
      rw [hP2def, Sylow.coe_mapSurjective, hP1]
    have hP2c : Nat.card P2 = 4 :=
      A7.nat_card_sylow_two_of_card_sixty SteinbergCB.nat_card_alternating_five P2
    have hSbe : Sb = (P2 : Subgroup ↥(alternatingGroup (Fin 5))).map
        (alternatingGroup (Fin 5)).subtype := by
      rw [hP2, Subgroup.map_map]
      rfl
    rw [hSbe, Subgroup.card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective]
    exact hP2c
  have hcSb : ∀ s ∈ Sb, c * s * c⁻¹ ∈ Sb := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨⟨k, hkK⟩ * t * (⟨k, hkK⟩ : ↥K)⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    push_cast
    exact (Subgroup.mem_normalizer_iff.mp hkN _).mp ht
  have hSbφ : ∀ (t : G) (ht : t ∈ (S : Subgroup G) ⊓ K), φ ⟨t, hKH ht.2⟩ ∈ Sb := by
    intro t ht
    rw [hφK t ht.2]
    exact ⟨⟨t, ht.2⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  set R := pCoreOf 2 M ⊓ H with hRdef
  have hR2 : IsPGroup 2 R :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hRconj : ∀ x ∈ M, x ∈ H → ∀ r ∈ R, x * r * x⁻¹ ∈ R := fun x hxM hxH r hr =>
    ⟨(Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hxM) r).mp hr.1,
      H.mul_mem (H.mul_mem hxH hr.2) (H.inv_mem hxH)⟩
  have hVR : V ≤ R := by
    have hVL : V ≤ L := by
      rw [← commutator_eq_of_hyp1223 hH, Subgroup.commutator_le]
      intro v hv l hl
      rw [commutatorElement_def]
      exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTM (hVT hv)) l).mp hl) (L.inv_mem hl)
    have h1 : V ≤ pCoreOf 2 L :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL (le_normalizer_of_hyp1223 hH)
        (B2F.isPGroup_of_isElemAbelian hVe)
    have h2 : pCoreOf 2 L ≤ pCoreOf 2 M :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans Subgroup.le_normalizer)
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact fun v hv => ⟨h2 (h1 hv), hVH hv⟩
  set R₀ := (R.subgroupOf H).map φ with hR₀def
  have hR₀2 : IsPGroup 2 R₀ := (hR2.comap_of_injective H.subtype H.subtype_injective).map φ
  have hR₀S : ∀ s ∈ Sb, ∀ x ∈ R₀, s * x * s⁻¹ ∈ R₀ := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨r, hr, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht hr
    have htH : (t : G) ∈ H := hKH t.2
    refine ⟨⟨t, htH⟩ * r * (⟨t, htH⟩ : ↥H)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      push_cast
      exact hRconj _ (hTM ht.1) htH _ hr
    · rw [map_mul, map_mul, map_inv, hφK t t.2]
  have hR₀c : ∀ x ∈ R₀, c * x * c⁻¹ ∈ R₀ := by
    rintro _ ⟨r, hr, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr
    refine ⟨⟨k, hkH⟩ * r * (⟨k, hkH⟩ : ↥H)⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      push_cast
      exact hRconj _ hkM hkH _ hr
    · rw [map_mul, map_mul, map_inv, hφK k hkK]
  have hR₀Sb : R₀ ≤ Sb := le_of_normalizes hSbA hSb4 hcSb hc3 hc1 hR₀2 hR₀S hR₀c
  have hφR : ∀ (r : G) (hr : r ∈ R), φ ⟨r, hr.2⟩ ∈ Sb := fun r hr =>
    hR₀Sb ⟨⟨r, hr.2⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  obtain ⟨a, haV, ha1⟩ : ∃ a, ∃ haV : a ∈ V, φ ⟨a, hVH haV⟩ ≠ 1 := by
    by_contra h
    push Not at h
    apply hVO
    intro v hv
    rw [← hCT]
    exact ⟨hVT hv, hφker v (hVH hv) (h v hv)⟩
  have haφ : φ ⟨a, hVH haV⟩ ∈ Sb := hφR a (hVR haV)
  obtain ⟨u, huV, hu1, huφ⟩ : ∃ u, ∃ huV : u ∈ V, u ≠ 1 ∧ φ ⟨u, hVH huV⟩ = 1 := by
    have hcard := B1More.card_map_mul_card_inf_ker (V.subgroupOf H) φ
    have hV'c : Nat.card (V.subgroupOf H) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv
    have hmap : (V.subgroupOf H).map φ ≤ Sb := by
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hv
      exact hφR v (hVR hv)
    have hle : Nat.card ((V.subgroupOf H).map φ) ≤ 4 := hSb4 ▸ Subgroup.card_le_of_le hmap
    by_contra hno
    push Not at hno
    have hbot : V.subgroupOf H ⊓ φ.ker = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      rw [Subgroup.mem_bot]
      by_contra hx
      exact hno x (Subgroup.mem_subgroupOf.mp hx1) (fun h => hx (Subtype.ext h)) hx2
    rw [hbot, Subgroup.card_bot, mul_one, hV'c] at hcard
    exact hV4 (hcard ▸ hle)
  have huW : u ∈ Subgroup.centralizer (W : Set G) := hφker u (hVH huV) huφ
  have huK : ∀ b ∈ H, b * u * b⁻¹ ∈ Subgroup.normalizer (V : Set G) := fun b hb =>
    (mem_kerIn.mp (hker ⟨hVH huV, huW⟩) b hb).2
  set A := CFSG.conjugate V k⁻¹ with hAdef
  have hmemA : ∀ x, x ∈ A ↔ k⁻¹ * x * k ∈ V := fun x => by
    rw [hAdef, BlueprintB2.mem_conjugate_iff, inv_inv]
  have hAR : A ≤ R := by
    intro x hx
    have h1 := hRconj k hkM hkH _ (hVR ((hmemA x).mp hx))
    rwa [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at h1
  have hVA2 : IsPGroup 2 ↥(V ⊔ A) := hR2.to_le (sup_le hVR hAR)
  have hAe : IsElemAbelian 2 A := isElemAbelian_conjugate hVe k⁻¹
  have hcard : Nat.card V = Nat.card A := (card_conjugate V k⁻¹).symm
  have hNA : ∀ g : G, k⁻¹ * g * k ∈ Subgroup.normalizer (V : Set G) →
      g ∈ Subgroup.normalizer (A : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
    rw [hmemA, hmemA, Subgroup.mem_normalizer_iff.mp hg]
    rw [show k⁻¹ * g * k * (k⁻¹ * z * k) * (k⁻¹ * g * k)⁻¹ = k⁻¹ * (g * z * g⁻¹) * k by group]
  have hTIV : IsTISetIn V ⊤ := ⟨le_top, fun g _ hg => eq_bot_iff.mpr fun x hx => by
    obtain ⟨hx1, hx2⟩ := hx
    by_contra hne
    exact hg (mem_normalizer_of_TI hTI hx1 (fun h => hne (h ▸ Subgroup.one_mem _))
      (mem_conjSubgroup_iff.mp hx2))⟩
  have hTIA : IsTISetIn A ⊤ := ⟨le_top, fun g _ hg => eq_bot_iff.mpr fun x hx => by
    obtain ⟨hx1, hx2⟩ := hx
    by_contra hne
    have hx1' := (hmemA x).mp hx1
    have hx2' := (hmemA _).mp (mem_conjSubgroup_iff.mp hx2)
    apply hg
    refine hNA g (mem_normalizer_of_TI hTI hx1' (fun h => hne ?_) ?_)
    · have : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
      rw [this, h]
      simp
    · rw [show k⁻¹ * g * k * (k⁻¹ * x * k) * (k⁻¹ * g * k)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k by group]
      exact hx2'⟩
  have hcross : ∀ g : G, V ≠ conjSubgroup A g → conjSubgroup A g ⊓ V = ⊥ := by
    intro g hg
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    by_contra hne
    have hx1' := (hmemA _).mp (mem_conjSubgroup_iff.mp hx1)
    have hN : k⁻¹ * g ∈ Subgroup.normalizer (V : Set G) :=
      mem_normalizer_of_TI hTI hx2 (fun h => hne (h ▸ Subgroup.one_mem _))
        (by rw [show k⁻¹ * g * x * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * x * g⁻¹) * k by group]; exact hx1')
    apply hg
    ext z
    rw [mem_conjSubgroup_iff, hmemA, Subgroup.mem_normalizer_iff.mp hN z]
    rw [show k⁻¹ * g * z * (k⁻¹ * g)⁻¹ = k⁻¹ * (g * z * g⁻¹) * k by group]
  have hcross' : ∀ g : G, A ≠ conjSubgroup V g → conjSubgroup V g ⊓ A = ⊥ := by
    intro g hg
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    by_contra hne
    have hx1' := mem_conjSubgroup_iff.mp hx1
    have hx2' := (hmemA x).mp hx2
    have hN : g * k ∈ Subgroup.normalizer (V : Set G) := by
      refine mem_normalizer_of_TI hTI hx2' (fun h => hne ?_) ?_
      · have : x = k * (k⁻¹ * x * k) * k⁻¹ := by group
        rw [this, h]
        simp
      · rw [show g * k * (k⁻¹ * x * k) * (g * k)⁻¹ = g * x * g⁻¹ by group]
        exact hx1'
    apply hg
    ext z
    rw [hmemA, mem_conjSubgroup_iff, Subgroup.mem_normalizer_iff.mp hN]
    rw [show g * k * (k⁻¹ * z * k) * (g * k)⁻¹ = g * z * g⁻¹ by group]
  have hU : ASInputs.tiU V A ≠ ⊥ := by
    intro h
    have hu : u ∈ ASInputs.tiU V A :=
      ⟨huV, hNA u (by simpa using huK k⁻¹ (H.inv_mem hkH))⟩
    rw [h, Subgroup.mem_bot] at hu
    exact hu1 hu
  have hU' : ASInputs.tiU A V ≠ ⊥ := by
    intro h
    have hu : k * u * k⁻¹ ∈ ASInputs.tiU A V :=
      ⟨(hmemA _).mpr (by rw [show k⁻¹ * (k * u * k⁻¹) * k = u by group]; exact huV),
        huK k hkH⟩
    rw [h, Subgroup.mem_bot] at hu
    apply hu1
    calc u = k⁻¹ * (k * u * k⁻¹) * k := by group
      _ = 1 := by rw [hu]; group
  have hVNA := le_normalizer_of_isPGroup hVe hAe hcard hTIV hTIA hcross hU hVA2
  have hANV := le_normalizer_of_isPGroup hAe hVe hcard.symm hTIA hTIV hcross' hU'
    (by rwa [sup_comm])
  have hcommVA : ∀ v ∈ V, ∀ x ∈ A, v * x = x * v := by
    intro v hv x hx
    rcases hTI k⁻¹ with hAV | hAV
    · have hAV' : A = V := hAV
      have hx' : x ∈ V := hAV' ▸ hx
      exact congrArg Subtype.val (hVe.1.is_comm.comm ⟨v, hv⟩ ⟨x, hx'⟩)
    · have hAV' : V ⊓ A = ⊥ := hAV
      have h1 : v * x * v⁻¹ * x⁻¹ ∈ A :=
        A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVNA hv) x).mp hx) (A.inv_mem hx)
      have h2 : v * x * v⁻¹ * x⁻¹ ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (hANV hx) v⁻¹).mp (V.inv_mem hv)
        rw [show v * x * v⁻¹ * x⁻¹ = v * (x * v⁻¹ * x⁻¹) by group]
        exact V.mul_mem hv this
      have h3 : v * x * v⁻¹ * x⁻¹ ∈ V ⊓ A := ⟨h2, h1⟩
      rw [hAV', Subgroup.mem_bot] at h3
      calc v * x = (v * x * v⁻¹ * x⁻¹) * (x * v) := by group
        _ = x * v := by rw [h3, one_mul]
  set b := k * a * k⁻¹ with hbdef
  have hbA : b ∈ A := (hmemA b).mpr (by
    rw [hbdef, show k⁻¹ * (k * a * k⁻¹) * k = a by group]
    exact haV)
  have hbH : b ∈ H := H.mul_mem (H.mul_mem hkH (hVH haV)) (H.inv_mem hkH)
  have hφb : φ ⟨b, hbH⟩ = c * φ ⟨a, hVH haV⟩ * c⁻¹ := by
    have e : (⟨b, hbH⟩ : ↥H) = ⟨k, hkH⟩ * ⟨a, hVH haV⟩ * (⟨k, hkH⟩ : ↥H)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hφK k hkK]
  have hbφ : φ ⟨b, hbH⟩ ∈ Sb := hφR b (hAR hbA)
  have hab : φ ⟨b, hbH⟩ ≠ φ ⟨a, hVH haV⟩ := by
    rw [hφb]
    exact conj_ne hSbA hSb4 hcSb hc3 hc1 haφ ha1
  have hb1 : φ ⟨b, hbH⟩ ≠ 1 := by
    rw [hφb]
    intro h
    exact ha1 (conj_eq_one_iff.mp h)
  obtain ⟨a', -, ha'φ⟩ := haφ
  obtain ⟨b', -, hb'φ⟩ := hbφ
  have hlift : ∀ (x : ↥K) (y : G) (hy : y ∈ H), A7.kBar eK x = φ ⟨y, hy⟩ →
      ∀ w ∈ W, (x : G) * w * (x : G)⁻¹ = y * w * y⁻¹ := by
    intro x y hy hxy w hw
    have hxH : (x : G) ∈ H := hKH x.2
    have h1 : φ (⟨x, hxH⟩⁻¹ * ⟨y, hy⟩) = 1 := by
      rw [map_mul, map_inv, ← hxy]
      have : φ ⟨x, hxH⟩ = A7.kBar eK x := hφK x x.2
      rw [this, inv_mul_cancel]
    have h2 := hφker _ _ h1
    have h3 := Subgroup.mem_centralizer_iff.mp h2 w hw
    push_cast at h3
    calc (x : G) * w * (x : G)⁻¹ = (x : G) * (w * ((x : G)⁻¹ * y)) * ((x : G)⁻¹ * y)⁻¹ *
          (x : G)⁻¹ := by group
      _ = (x : G) * (((x : G)⁻¹ * y) * w) * ((x : G)⁻¹ * y)⁻¹ * (x : G)⁻¹ := by rw [h3]
      _ = y * w * y⁻¹ := by group
  have ha'W := hlift a' a (hVH haV) ha'φ
  have hb'W := hlift b' b hbH hb'φ
  have hquad : ∀ w ∈ W, (b' : G) * (w * a' * w⁻¹ * (a' : G)⁻¹) * (b' : G)⁻¹ =
      w * a' * w⁻¹ * (a' : G)⁻¹ := by
    intro w hw
    have hw' : w⁻¹ ∈ W := W.inv_mem hw
    have e1 : w * (a' : G) * w⁻¹ * (a' : G)⁻¹ = w * a * w⁻¹ * a⁻¹ := by
      have := ha'W _ hw'
      calc w * (a' : G) * w⁻¹ * (a' : G)⁻¹ = w * ((a' : G) * w⁻¹ * (a' : G)⁻¹) := by group
        _ = w * (a * w⁻¹ * a⁻¹) := by rw [this]
        _ = w * a * w⁻¹ * a⁻¹ := by group
    have hxV : w * a * w⁻¹ * a⁻¹ ∈ V :=
      V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTV (hWT hw)) a).mp haV) (V.inv_mem haV)
    have hxW : w * a * w⁻¹ * a⁻¹ ∈ W := by
      have h1 : a * w⁻¹ * a⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hHW (hVH haV)) _).mp hw'
      rw [show w * a * w⁻¹ * a⁻¹ = w * (a * w⁻¹ * a⁻¹) by group]
      exact W.mul_mem hw h1
    rw [e1, hb'W _ hxW]
    have := (hcommVA _ hxV b hbA).symm
    calc b * (w * a * w⁻¹ * a⁻¹) * b⁻¹ = (w * a * w⁻¹ * a⁻¹) * b * b⁻¹ := by rw [this]
      _ = w * a * w⁻¹ * a⁻¹ := by group
  obtain ⟨W₁, hW₁, hW₁W⟩ : ∃ W₁ : Subgroup G, IsA5ModuleUnder K W₁ ∧ W₁ ≤ W := by
    have hcW : ⁅W, K⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro w hw x hx
      rw [commutatorElement_def]
      have := (Subgroup.mem_normalizer_iff.mp (hHW (hKH hx)) w⁻¹).mp (W.inv_mem hw)
      rw [show w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) by group]
      exact W.mul_mem hw this
    rcases hA5 with h | ⟨W₁, W₂, h1, -, -, hsum⟩
    · exact ⟨_, h, hcW⟩
    · exact ⟨W₁, h1, (le_sup_left.trans hsum.le).trans hcW⟩
  have hW' : K ≤ Subgroup.normalizer (W₁ : Set G) ∧
      ∃ π : alternatingGroup (Fin 5) →* autOn K W₁, Function.Surjective π ∧
        (∀ (γ : alternatingGroup (Fin 5)) (m : G6.PermMod 5), m ∈ G6.coreMod 5 →
          G6.permAct 5 (γ : Equiv.Perm (Fin 5)) m ∈ G6.coreMod 5) ∧
        ∃ β : (⊤ : Subgroup W₁) →* (FFModel.altDn 5).sec ⧸
          (FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec,
          Function.Surjective β ∧
          ∀ (γ : alternatingGroup (Fin 5)) (u : (⊤ : Subgroup W₁)) (m : G6.coreMod 5)
            (hu : ((π γ : autOn K W₁) : MulAut W₁) (u : W₁) ∈ (⊤ : Subgroup W₁))
            (hm : G6.permAct 5 (γ : Equiv.Perm (Fin 5)) (m : G6.PermMod 5) ∈ G6.coreMod 5),
            β u = QuotientGroup.mk m →
              β ⟨((π γ : autOn K W₁) : MulAut W₁) (u : W₁), hu⟩ =
                QuotientGroup.mk
                  ⟨G6.permAct 5 (γ : Equiv.Perm (Fin 5)) (m : G6.PermMod 5), hm⟩ := by
    obtain ⟨hKW, hcomm, π, hπs, -, -, -, -, hsec, -, β, hβs, -, hβe⟩ := hW₁
    exact ⟨hKW, π, hπs, hsec, β, hβs, hβe⟩
  obtain ⟨hKW₁, π, hπs, hsec, β, hβs, hβe⟩ := hW'
  set f : ↥K →* autOn K W₁ := (A4.actionOn W₁ K hKW₁).codRestrict (autOn K W₁)
    (fun x => (A4.mem_autOn_iff hKW₁).mpr ⟨x, rfl⟩) with hfdef
  have hfw : ∀ (x : ↥K) (w : ↥W₁),
      (((f x : autOn K W₁) : MulAut ↥W₁) w : G) = x * w * (x : G)⁻¹ := fun _ _ => rfl
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (A4.mem_autOn_iff hKW₁).mp hy
    exact ⟨x, rfl⟩
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hmk := A7.altDn_five_mk_injective
  have hπi : Function.Injective π := by
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple π.ker (MonoidHom.normal_ker π)
      with hk' | hk'
    · exact (MonoidHom.ker_eq_bot_iff π).mp hk'
    · exfalso
      obtain ⟨γ₀, hγ₀s, m₀, hm₀, i₀, hi₀⟩ := exists_moved
      set m : G6.coreMod 5 := ⟨Multiplicative.ofAdd m₀, G6.mem_coreMod.mpr hm₀⟩ with hmdef
      obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
      set γ : alternatingGroup (Fin 5) := ⟨γ₀, Equiv.Perm.mem_alternatingGroup.mpr hγ₀s⟩
      have hγ : π γ = 1 := (MonoidHom.mem_ker).mp (hk' ▸ Subgroup.mem_top γ)
      have hm' := hsec γ m m.2
      have h1 := hβe γ u m (Subgroup.mem_top _) hm' hu
      have e : (⟨((π γ : autOn K W₁) : MulAut W₁) (u : W₁), Subgroup.mem_top _⟩ :
          (⊤ : Subgroup W₁)) = u := by
        apply Subtype.ext
        rw [hγ]
        rfl
      rw [e, hu] at h1
      have h2 := congrArg (fun y : G6.coreMod 5 => Multiplicative.toAdd (y : G6.PermMod 5) i₀)
        (hmk h1)
      simp only [hmdef, G6.permAct_apply] at h2
      exact hi₀ h2.symm
  have hfk : ∀ x : ↥K, f x = 1 ↔ A7.kBar eK x = 1 := by
    have hback : ∀ x : ↥K, A7.kBar eK x = 1 → f x = 1 := by
      intro x hx
      apply Subtype.ext
      exact (A4.actionOn_eq_one_iff hKW₁ x).mpr
        (Subgroup.centralizer_le hW₁W (hkBar1 x hx).2)
    refine fun x => ⟨fun hx => ?_, hback x⟩
    by_contra hne
    have hN : (f.ker.map (A7.kHom eK)).Normal :=
      (MonoidHom.normal_ker f).map _ (A7.kHom_surjective eK)
    have hNt : f.ker.map (A7.kHom eK) = ⊤ := by
      rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple _ hN with h | h
      · exfalso
        have : A7.kHom eK x ∈ f.ker.map (A7.kHom eK) := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        apply hne
        show ((A7.kHom eK x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = 1
        rw [this]
        rfl
      · exact h
    have hf1 : ∀ y : ↥K, f y = 1 := by
      intro y
      have : A7.kHom eK y ∈ f.ker.map (A7.kHom eK) := by rw [hNt]; trivial
      obtain ⟨n, hn, hny⟩ := this
      have h1 : A7.kBar eK (n⁻¹ * y) = 1 := by
        show ((A7.kHom eK (n⁻¹ * y) : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) = 1
        rw [map_mul, map_inv, hny, inv_mul_cancel]
        rfl
      have h2 := hback _ h1
      calc f y = f n * f (n⁻¹ * y) := by rw [← map_mul]; group
        _ = 1 := by rw [MonoidHom.mem_ker.mp hn, h2, one_mul]
    apply hc1
    have : π (1 : alternatingGroup (Fin 5)) = π ⟨c, A7.kBar_mem eK _⟩ := by
      obtain ⟨y, hy⟩ := hfs (π ⟨c, A7.kBar_mem eK _⟩)
      rw [map_one, ← hy, hf1]
    have := congrArg Subtype.val (hπi this)
    exact this.symm
  obtain ⟨γ₁, hγ₁⟩ := hπs (f a')
  obtain ⟨γ₂, hγ₂⟩ := hπs (f b')
  have hfeq : ∀ x y : ↥K, A7.kBar eK x = A7.kBar eK y → f x = f y := by
    intro x y h
    have h1 : A7.kBar eK (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 := (hfk _).mpr h1
    calc f x = f x * f (x⁻¹ * y) := by rw [h2, mul_one]
      _ = f y := by rw [← map_mul]; group
  have hα₁ : A7.kBar eK a' ∈ Sb := ha'φ ▸ hφR a (hVR haV)
  have hα₂ : A7.kBar eK b' ∈ Sb := hb'φ ▸ hφR b (hAR hbA)
  have hsq : ∀ (γ : alternatingGroup (Fin 5)) (x : ↥K), π γ = f x → A7.kBar eK x ∈ Sb →
      (γ : Equiv.Perm (Fin 5)) * γ = 1 := by
    intro γ x hγ hx
    have h1 : π (γ * γ) = π 1 := by
      rw [map_mul, hγ, ← map_mul, map_one]
      exact (hfk _).mpr (by rw [map_mul]; exact mul_self_of_card_four hSbA hSb4 hx)
    exact congrArg Subtype.val (hπi h1)
  have hne1 : ∀ (γ : alternatingGroup (Fin 5)) (x : ↥K), π γ = f x → A7.kBar eK x ≠ 1 →
      (γ : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro γ x hγ hx h
    have h1 : γ = 1 := Subtype.ext h
    rw [h1, map_one, eq_comm, hfk] at hγ
    exact hx hγ
  have hγ₁₁ := hne1 γ₁ a' hγ₁ (by rw [ha'φ]; exact ha1)
  have hγ₂₁ := hne1 γ₂ b' hγ₂ (by rw [hb'φ]; exact hb1)
  have hγ₁₂ : (γ₁ : Equiv.Perm (Fin 5)) ≠ γ₂ := by
    intro h
    have h1 : f a' = f b' := by rw [← hγ₁, ← hγ₂, Subtype.ext h]
    have h2 : f (a'⁻¹ * b') = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := (hfk _).mp h2
    rw [map_mul, map_inv, inv_mul_eq_one, ha'φ, hb'φ] at h3
    exact hab h3.symm
  have hcomm₁₂ : (γ₁ : Equiv.Perm (Fin 5)) * γ₂ = γ₂ * γ₁ := by
    have h1 : π (γ₁ * γ₂) = π (γ₂ * γ₁) := by
      rw [map_mul, map_mul, hγ₁, hγ₂, ← map_mul, ← map_mul]
      exact hfeq _ _ (by rw [map_mul, map_mul]; exact comm_of_card_four hSbA hSb4 hα₁ hα₂)
    exact congrArg Subtype.val (hπi h1)
  obtain ⟨m₀, hm₀, i₀, hi₀⟩ := not_quadratic γ₁ γ₂
    ⟨Equiv.Perm.mem_alternatingGroup.mp γ₁.2, Equiv.Perm.mem_alternatingGroup.mp γ₂.2,
      hsq γ₁ a' hγ₁ hα₁, hsq γ₂ b' hγ₂ hα₂, hγ₁₁, hγ₂₁, hγ₁₂, hcomm₁₂⟩
  set m : G6.coreMod 5 := ⟨Multiplicative.ofAdd m₀, G6.mem_coreMod.mpr hm₀⟩ with hmdef
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk m)
  have hm1 := hsec γ₁ m m.2
  have h1 := hβe γ₁ u m (Subgroup.mem_top _) hm1 hu
  set u' : ↥W₁ := ((π γ₁ : autOn K W₁) : MulAut ↥W₁) (u : ↥W₁) with hu'def
  set x : ↥W₁ := (u : ↥W₁) * u'⁻¹ with hxdef
  have hx : ((π γ₂ : autOn K W₁) : MulAut ↥W₁) x = x := by
    apply Subtype.ext
    rw [hγ₂, hfw]
    have hu'v : (u' : G) = a' * ((u : ↥W₁) : G) * (a' : G)⁻¹ := by rw [hu'def, hγ₁, hfw]
    have e : (x : G) = ((u : ↥W₁) : G) * (a' : G) * ((u : ↥W₁) : G)⁻¹ * (a' : G)⁻¹ := by
      rw [hxdef, Subgroup.coe_mul, Subgroup.coe_inv, hu'v]
      group
    rw [e]
    exact hquad _ (hW₁W (u : ↥W₁).2)
  set n : G6.coreMod 5 :=
    m * ⟨G6.permAct 5 (γ₁ : Equiv.Perm (Fin 5)) (m : G6.PermMod 5), hm1⟩⁻¹ with hndef
  have hβx : β ⟨x, Subgroup.mem_top _⟩ = QuotientGroup.mk n := by
    have e : (⟨x, Subgroup.mem_top _⟩ : (⊤ : Subgroup ↥W₁)) =
        u * (⟨u', Subgroup.mem_top _⟩ : (⊤ : Subgroup ↥W₁))⁻¹ := rfl
    rw [e, map_mul, map_inv, hu, h1]
    rfl
  have hn2 := hsec γ₂ n n.2
  have h2 := hβe γ₂ ⟨x, Subgroup.mem_top _⟩ n (Subgroup.mem_top _) hn2 hβx
  have e2 : (⟨((π γ₂ : autOn K W₁) : MulAut ↥W₁) x, Subgroup.mem_top _⟩ :
      (⊤ : Subgroup ↥W₁)) = ⟨x, Subgroup.mem_top _⟩ := Subtype.ext hx
  rw [e2, hβx] at h2
  have h3 := hmk h2
  have h4 := congrArg (fun y : G6.coreMod 5 => Multiplicative.toAdd (y : G6.PermMod 5) i₀) h3
  simp only [hndef, hmdef, Subgroup.coe_mul, Subgroup.coe_inv, G6.permAct_apply, toAdd_mul,
    toAdd_inv, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply] at h4
  apply hi₀
  exact zmod_two_sum_eq_zero _ _ _ _ h4

end Lem19S

end CFSG.Quasithin.H13
