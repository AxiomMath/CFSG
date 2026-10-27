module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23MX
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.Quasithin.H13

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

structure IsVFacts (M L : Subgroup G) : Prop where
  card : Nat.card ↥(pCoreOf 2 L) = 16
  sq : ∀ v ∈ pCoreOf 2 L, v * v = 1
  comm : ∀ v ∈ pCoreOf 2 L, ∀ w ∈ pCoreOf 2 L, v * w = w * v
  irred : ∀ W : Subgroup G, W ≤ pCoreOf 2 L → L ≤ Subgroup.normalizer (W : Set G) →
    W = ⊥ ∨ W = pCoreOf 2 L
  cent : M ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) ≤ pCoreOf 2 L
  L_le : L ≤ M
  normal : M ≤ Subgroup.normalizer (L : Set G)
  card_L : Nat.card L = 960

theorem isVFacts_of_setting
    (h526 : Stmt5_2_6) (h527 : Stmt5_2_7) (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz)
    (hU4 : Stmt5_2_8_U4) (hsp : Stmt5_2_8_special) (hQ : Stmt5_2_8_Q)
    {T M L V H B D L₂ M2 : Subgroup G} {n : ℕ} {π : ↥M2 →* Equiv.Perm (Fin 7)}
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hM23 : IsOfTypeM23 M L H B D T)
    (hS : IsM23Setting T H M2 π) : IsVFacts M L := by
  obtain ⟨hbl, hLin, h16, hUQ, hL960⟩ := setting_L_facts h526 h1284 hSz hU4 hsp hQ hyp hM23 hS
  have hVsq := hbl.1.2.2.1
  rw [hUQ] at hVsq
  exact ⟨h16, fun v hv => by rw [← sq]; exact hVsq.2 v hv,
    fun v hv w hw => (Subgroup.mem_centralizer_iff.mp (hVsq.1 hw).2) v hv,
    fun W hW hWL => eq_bot_or_eq_of_le_pCoreOf_L hbl hLin h16 hUQ hW hWL,
    centralizer_le_pCoreOf_L h527 hyp h16, hyp.L_le, hyp.normal, hL960⟩

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_centralizerModO2 {L : Subgroup G} {x : G}
    (hx : x ∈ centralizerModO2 L) {l : G} (hl : l ∈ L) : x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
  hx.2.2 l hl

theorem eq_one_of_mem_pCoreOf_L_of_commute {M L : Subgroup G} (hV : IsVFacts M L) {x : G}
    (hxM : x ∈ M) (hxC : x ∈ centralizerModO2 L) (hx3 : orderOf x = 3) {v : G}
    (hv : v ∈ pCoreOf 2 L) (hxv : x * v = v * x) : v = 1 := by
  set W := pCoreOf 2 L ⊓ Subgroup.centralizer ({x} : Set G) with hW
  have hmemW : ∀ w, w ∈ W ↔ w ∈ pCoreOf 2 L ∧ x * w = w * x := by
    intro w
    rw [hW, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2.symm⟩
  have hVN : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hWL : L ≤ Subgroup.normalizer (W : Set G) := by
    intro l hl
    have key : ∀ l ∈ L, ∀ w ∈ W, l * w * l⁻¹ ∈ W := by
      intro l hl w hw
      obtain ⟨hwV, hxw⟩ := (hmemW w).mp hw
      have hlw : l * w * l⁻¹ ∈ pCoreOf 2 L := (Subgroup.mem_normalizer_iff.mp (hVN hl) w).mp hwV
      refine (hmemW _).mpr ⟨hlw, ?_⟩
      set c := x * l * x⁻¹ * l⁻¹ with hc
      have hcV : c ∈ pCoreOf 2 L := commutator_mem_pCoreOf_of_centralizerModO2 hxC hl
      have hxl : x * l = c * l * x := by rw [hc]; group
      have hcomm := hV.comm c hcV _ hlw
      calc x * (l * w * l⁻¹) = (x * l) * w * l⁻¹ := by group
        _ = c * l * (x * w) * l⁻¹ := by rw [hxl]; group
        _ = c * l * (w * x) * l⁻¹ := by rw [hxw]
        _ = c * (l * w * l⁻¹) * (l * x * l⁻¹) := by group
        _ = (l * w * l⁻¹) * c * (l * x * l⁻¹) := by rw [hcomm]
        _ = (l * w * l⁻¹) * (c * l * x) * l⁻¹ := by group
        _ = (l * w * l⁻¹) * (x * l) * l⁻¹ := by rw [← hxl]
        _ = (l * w * l⁻¹) * x := by group
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact key l hl w
    · intro h
      have := key l⁻¹ (L.inv_mem hl) _ h
      simpa [mul_assoc] using this
  rcases hV.irred W inf_le_left hWL with hb | heq
  · have : v ∈ W := (hmemW v).mpr ⟨hv, hxv⟩
    rw [hb] at this
    exact (Subgroup.mem_bot.mp this)
  · exfalso
    have hxV : x ∈ pCoreOf 2 L := by
      refine hV.cent (Subgroup.mem_inf.mpr ⟨hxM, ?_⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have : w ∈ W := heq ▸ hw
      exact ((hmemW w).mp this).2.symm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨x, hxV⟩
    have hd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hk
      simpa using this)
    rw [hx3] at hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at this

theorem exists_commute_mul_mem_coset {M L : Subgroup G} (hV : IsVFacts M L) {x : G} (hxM : x ∈ M)
    (hxC : x ∈ centralizerModO2 L) (hx3 : orderOf x = 3) {l : G} (hl : l ∈ L) :
    ∃ v ∈ pCoreOf 2 L, x * (l * v) = l * v * x := by
  set V' := pCoreOf 2 L with hV'
  let _ := commGroupOfComm V' hV.comm
  have hxN : x ∈ Subgroup.normalizer (V' : Set G) := hxC.2.1
  let ρ : ↥V' →* ↥V' :=
    { toFun := fun v => ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.mp hxN v).mp v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun v w => Subtype.ext (by simp [mul_assoc]) }
  let ψ : ↥V' →* ↥V' := MonoidHom.id ↥V' * ρ
  have hψ : ∀ v : ↥V', ((ψ v : ↥V') : G) = v * (x * v * x⁻¹) := fun v => rfl
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    have h1 : (v : G) * (x * v * x⁻¹) = 1 := by
      rw [← hψ]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hv)
    have hvv : (v : G) * v = 1 := hV.sq v v.2
    have h2 : x * v * x⁻¹ = v := by
      have e : x * v * x⁻¹ = (v : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [e, inv_eq_of_mul_eq_one_right hvv]
    have hxv : x * (v : G) = v * x := by
      calc x * (v : G) = x * v * x⁻¹ * x := by group
        _ = v * x := by rw [h2]
    exact Subgroup.mem_bot.mpr (Subtype.ext (eq_one_of_mem_pCoreOf_L_of_commute hV hxM hxC hx3
      v.2 hxv))
  have hψsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψinj
  have hVN : L ≤ Subgroup.normalizer (V' : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have ha : l⁻¹ * (x * l * x⁻¹) ∈ V' := by
    have h1 := commutator_mem_pCoreOf_of_centralizerModO2 hxC hl
    have h2 := (Subgroup.mem_normalizer_iff.mp (hVN (L.inv_mem hl)) _).mp h1
    have e : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
    rwa [e] at h2
  obtain ⟨v, hv⟩ := hψsurj ⟨_, ha⟩
  have hv' : (v : G) * (x * v * x⁻¹) = l⁻¹ * (x * l * x⁻¹) := by
    rw [← hψ, hv]
  refine ⟨v, v.2, ?_⟩
  have hsq : (x * v * x⁻¹) * (x * v * x⁻¹) = 1 := by
    have := hV.sq v v.2
    calc (x * v * x⁻¹) * (x * v * x⁻¹) = x * ((v : G) * v) * x⁻¹ := by group
      _ = 1 := by rw [this]; group
  have key : x * l * x⁻¹ = l * v * (x * v * x⁻¹) := by
    have e : x * l * x⁻¹ = l * (l⁻¹ * (x * l * x⁻¹)) := by group
    rw [e, ← hv']
    group
  calc x * (l * v) = (x * l * x⁻¹) * (x * v * x⁻¹) * x := by group
    _ = l * v * ((x * v * x⁻¹) * (x * v * x⁻¹)) * x := by rw [key]; group
    _ = l * v * x := by rw [hsq, mul_one]

theorem card_centralizer_inf_L {M L : Subgroup G} (hV : IsVFacts M L) {x : G} (hxM : x ∈ M)
    (hxC : x ∈ centralizerModO2 L) (hx3 : orderOf x = 3) :
    Nat.card ↥(L ⊓ Subgroup.centralizer ({x} : Set G)) = 60 := by
  set C := L ⊓ Subgroup.centralizer ({x} : Set G) with hC
  have hmemC : ∀ g, g ∈ C ↔ g ∈ L ∧ x * g = g * x := by
    intro g
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  have hVN : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hdisj : Disjoint (pCoreOf 2 L) C := by
    rw [Subgroup.disjoint_def]
    intro g hgV hgC
    exact eq_one_of_mem_pCoreOf_L_of_commute hV hxM hxC hx3 hgV ((hmemC g).mp hgC).2
  have hsup : pCoreOf 2 L ⊔ C = L := by
    apply le_antisymm (sup_le (CFSG.LieType.BorelTits.pCoreOf_le 2 L) inf_le_left)
    intro l hl
    obtain ⟨v, hv, hcomm⟩ := exists_commute_mul_mem_coset hV hxM hxC hx3 hl
    have hlv : l * v ∈ C := (hmemC _).mpr ⟨L.mul_mem hl (CFSG.LieType.BorelTits.pCoreOf_le 2 L hv),
      hcomm⟩
    have e : l = v⁻¹ * (v * (l * v) * v⁻¹) := by group
    have e' : l = (l * v) * v⁻¹ := by group
    rw [e']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hlv)
      (Subgroup.mem_sup_left ((pCoreOf 2 L).inv_mem hv))
  have h := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (pCoreOf 2 L) C
    (inf_le_left.trans hVN) hdisj
  rw [hsup, hV.card_L, hV.card] at h
  omega

theorem eq_two_of_three_pow_mul_eq_144 {k m : ℕ} (h : 3 ^ k * m = 144) (hm : ¬ 3 ∣ m) :
    k = 2 := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  have hk : k < 6 := by
    by_contra hk
    have h6 : 3 ^ 6 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 3 ^ 6 * 1 ≤ 3 ^ k * m := Nat.mul_le_mul h6 hm0
    omega
  interval_cases k <;> omega

theorem exists_card_nine_le_centralizer {M M2 : Subgroup G}
    {π : ↥M2 →* Perm (Fin 7)} (hEM : preE9 M2 π ≤ M) (hE : Nat.card (preE9 M2 π) = 144)
    {x : G} (hxE : x ∈ preE9 M2 π) (hx3 : orderOf x = 3) :
    ∃ P : Subgroup G, P ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧ Nat.card P = 9 := by
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := preE9 M2 π with hEdef
  set x' : ↥E := ⟨x, hxE⟩
  have hx'3 : orderOf x' = 3 := by rw [← Subgroup.orderOf_coe]; exact hx3
  have hzp : IsPGroup 3 (Subgroup.zpowers x') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'3, pow_one])
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hcardQ : Nat.card (Q : Subgroup ↥E) = 9 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
    have h2 := Subgroup.card_mul_index (Q : Subgroup ↥E)
    rw [hk, hE] at h2
    have hk2 := eq_two_of_three_pow_mul_eq_144 h2 Q.not_dvd_index
    rw [hk, hk2]
    norm_num
  have hcomm : ∀ a b : ↥(Q : Subgroup ↥E), a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcardQ).is_comm.comm a b
  refine ⟨(Q : Subgroup ↥E).map E.subtype, ?_, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨hEM q.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx'Q : x' ∈ (Q : Subgroup ↥E) := hQ (Subgroup.mem_zpowers x')
    have := hcomm ⟨q, hq⟩ ⟨x', hx'Q⟩
    have := congrArg (fun z : ↥(Q : Subgroup ↥E) => ((z : ↥E) : G)) this
    simpa using this
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hcardQ]

theorem exists_le_centralizer_dvd_card {M L M2 : Subgroup G}
    {π : ↥M2 →* Perm (Fin 7)} (hV : IsVFacts M L) (hEM : preE9 M2 π ≤ M)
    (hE : Nat.card (preE9 M2 π) = 144) {x : G} (hxE : x ∈ preE9 M2 π) (hxM : x ∈ M)
    (hxC : x ∈ centralizerModO2 L) (hx3 : orderOf x = 3) :
    ∃ W : Subgroup G, W ≤ M ⊓ Subgroup.centralizer ({x} : Set G) ∧ 180 ∣ Nat.card W := by
  obtain ⟨P, hP, hP9⟩ := exists_card_nine_le_centralizer hEM hE hxE hx3
  have hCL := card_centralizer_inf_L hV hxM hxC hx3
  set C := L ⊓ Subgroup.centralizer ({x} : Set G)
  refine ⟨C ⊔ P, sup_le (le_inf (inf_le_left.trans hV.L_le) inf_le_right) hP, ?_⟩
  have h60 : 60 ∣ Nat.card ↥(C ⊔ P) := hCL ▸ Subgroup.card_dvd_of_le le_sup_left
  have h9 : 9 ∣ Nat.card ↥(C ⊔ P) := hP9 ▸ Subgroup.card_dvd_of_le le_sup_right
  have := Nat.lcm_dvd h60 h9
  rwa [show Nat.lcm 60 9 = 180 by norm_num] at this

end CFSG.Quasithin.H13
