module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Lift
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Mod
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6ParrottL2
public import CFSG.Quasithin.Background.CommVCommute

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

private theorem conjAct_conj_of_mem {P : Type*} [Group P] {L : Subgroup P} {x : P}
    (hx : x ∈ L) :
    conjAct L ⟨x, L.le_normalizer hx⟩ = MulAut.conj (⟨x, hx⟩ : ↥L) := by
  ext y
  rw [AutOn.coe_conjAct_apply, MulAut.conj_apply]
  rfl

private theorem apply_commV_eq_of_isQuadratic {A : Subgroup (MulAut V)} (hA : IsQuadratic A)
    {a b : MulAut V} (ha : a ∈ A) (hb : b ∈ A) (v : V) :
    b (a v * v⁻¹) = a v * v⁻¹ :=
  hA (Subgroup.subset_closure ⟨a, ha, v, rfl⟩) b hb

private theorem mem_center_of_conj_eq_one {X : Type*} [Group X] {z : X}
    (hz : MulAut.conj z = 1) : z ∈ center X := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 : z * g * z⁻¹ = g := by
    have := congrArg (fun τ : MulAut X => τ g) hz
    simpa [MulAut.conj_apply] using this
  calc g * z = z * g * z⁻¹ * z := by rw [h1]
    _ = z * g := by group

private theorem sq_eq_one_of_conj_sq_eq_one {X : Type*} [Group X] (hZ : center X = ⊥)
    {x : X} (h : MulAut.conj x * MulAut.conj x = 1) : x * x = 1 := by
  have hc : MulAut.conj (x * x) = 1 := by rw [map_mul]; exact h
  have hcent : x * x ∈ center X := mem_center_of_conj_eq_one hc
  rw [hZ] at hcent
  exact Subgroup.mem_bot.mp hcent

private theorem commute_of_card_four {G : Type*} [Group G] {A : Subgroup G}
    (hA4 : Nat.card A = 4) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) : a * b = b * a := by
  have hcard : Nat.card ↥A = 2 ^ 2 := by rw [hA4]; norm_num
  have hcomm : IsMulCommutative ↥A := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  exact congrArg Subtype.val (isMulCommutative_iff.mp hcomm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem exists_foote_data {L A : Subgroup (MulAut V)} (hZ : center ↥L = ⊥)
    (hX : L2AutFacts ↥L) (hAL : A ≤ normalizer (L : Set (MulAut V)))
    (hA4 : Nat.card A = 4) (hA2 : ∀ a ∈ A, a * a = 1)
    (hAC : A ⊓ centralizer (L : Set (MulAut V)) = ⊥) :
    ∃ (t : MulAut V) (ht : t ∈ A) (t₀ : ↥L),
      t ≠ 1 ∧ (t₀ : MulAut V) ≠ 1 ∧
      conjAct L ⟨t, hAL ht⟩ = MulAut.conj t₀ ∧
      t * (t₀ : MulAut V)⁻¹ ∈ centralizer (L : Set (MulAut V)) ∧
      (t₀ : MulAut V)⁻¹ * t ∈ centralizer (L : Set (MulAut V)) := by
  classical
  let N : Subgroup (MulAut V) := Subgroup.normalizer (L : Set (MulAut V))
  let K : Subgroup ↥N := A.subgroupOf N
  let α : ↥N →* MulAut ↥L := conjAct L
  let f : ↥K →* MulAut ↥L := α.domRestrict K
  have hfker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    change α y.1 = 1 at hy
    have hyA : ((y.1 : ↥N) : MulAut V) ∈ A := (Subgroup.mem_subgroupOf).1 y.2
    have hyC : ((y.1 : ↥N) : MulAut V) ∈ centralizer (L : Set (MulAut V)) :=
      (AutOn.conjAct_eq_one_iff (V := L) y.1).1 hy
    have hbot : ((y.1 : ↥N) : MulAut V) ∈ A ⊓ centralizer (L : Set (MulAut V)) :=
      ⟨hyA, hyC⟩
    rw [hAC] at hbot
    have hy1 : ((y.1 : ↥N) : MulAut V) = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext (Subtype.ext hy1)
  have hcardK : Nat.card ↥K = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv
  have hcardrange : Nat.card ↥f.range = 4 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hfker, hcardK, hA4] at h
    simpa using h
  have hW2 : ∀ w ∈ f.range, w * w = 1 := by
    intro w hw
    obtain ⟨y, rfl⟩ := hw
    have hyA : ((y.1 : ↥N) : MulAut V) ∈ A := (Subgroup.mem_subgroupOf).1 y.2
    have hsq : ((y.1 : ↥N) : MulAut V) * ((y.1 : ↥N) : MulAut V) = 1 := hA2 _ hyA
    have hsqN : y.1 * y.1 = 1 := Subtype.ext hsq
    change α y.1 * α y.1 = 1
    rw [← map_mul, hsqN, map_one]
  obtain ⟨w, hwmem, hwne, hwInn⟩ := hX.foote f.range hW2 hcardrange
  obtain ⟨y, hyw⟩ := hwmem
  obtain ⟨t₀, ht₀⟩ := hwInn
  let t : MulAut V := (y.1 : ↥N)
  have htN : t ∈ N := y.1.2
  have htA : t ∈ A := (Subgroup.mem_subgroupOf).1 y.2
  have ht1 : t ≠ 1 := by
    intro ht
    have hy1 : y.1 = 1 := Subtype.ext ht
    have hw1 : w = 1 := by
      rw [← hyw]
      change α y.1 = 1
      rw [hy1, map_one]
    exact hwne hw1
  have ht₀1 : (t₀ : MulAut V) ≠ 1 := by
    intro ht
    have ht0' : t₀ = 1 := Subtype.ext ht
    have hw1 : w = 1 := by rw [← ht₀, ht0', map_one]
    exact hwne hw1
  have hy_eq : y.1 = (⟨t, hAL htA⟩ : ↥N) := Subtype.ext rfl
  have hαt : conjAct L ⟨t, hAL htA⟩ = MulAut.conj t₀ := by
    calc conjAct L ⟨t, hAL htA⟩ = α y.1 := by rw [hy_eq]
      _ = f y := rfl
      _ = w := hyw
      _ = MulAut.conj t₀ := ht₀.symm
  have ht₀N : (t₀ : MulAut V) ∈ N := L.le_normalizer t₀.2
  have hαt₀ : conjAct L ⟨(t₀ : MulAut V), ht₀N⟩ = MulAut.conj t₀ :=
    conjAct_conj_of_mem t₀.2
  have ht₀sq : t₀ * t₀ = 1 := by
    have hconj : MulAut.conj (t₀ * t₀) = 1 := by
      have hsqN : (⟨t, hAL htA⟩ : ↥N) * ⟨t, hAL htA⟩ = 1 :=
        Subtype.ext (hA2 t htA)
      rw [map_mul, ← hαt, ← map_mul, hsqN, map_one]
    have hcent : t₀ * t₀ ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx := congrArg (fun φ : MulAut ↥L => φ x) hconj
      simp only [MulAut.conj_apply, MulAut.one_apply] at hx
      calc x * (t₀ * t₀) = ((t₀ * t₀) * x * (t₀ * t₀)⁻¹) * (t₀ * t₀) := by rw [hx]
        _ = (t₀ * t₀) * x := by group
    rw [hZ] at hcent
    exact Subgroup.mem_bot.mp hcent
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hA2 t htA)
  have ht₀inv : (t₀ : MulAut V)⁻¹ = (t₀ : MulAut V) :=
    inv_eq_of_mul_eq_one_right (congrArg (fun z : ↥L => (z : MulAut V)) ht₀sq)
  have ht0c : t * (t₀ : MulAut V)⁻¹ ∈ centralizer (L : Set (MulAut V)) := by
    have hNmul : t * (t₀ : MulAut V)⁻¹ ∈ N := N.mul_mem htN (N.inv_mem ht₀N)
    let z : ↥N := ⟨t * (t₀ : MulAut V)⁻¹, hNmul⟩
    have hz : conjAct L z = 1 := by
      have hαt' : conjAct L ⟨t, htN⟩ = MulAut.conj t₀ := by
        rwa [show (⟨t, htN⟩ : ↥N) = ⟨t, hAL htA⟩ from Subtype.ext rfl]
      have hz_eq : z = ⟨t, htN⟩ * ⟨(t₀ : MulAut V), ht₀N⟩⁻¹ := Subtype.ext rfl
      rw [hz_eq, map_mul, map_inv, hαt', hαt₀]
      simp
    exact (AutOn.conjAct_eq_one_iff z).1 hz
  have ht0cinv : (t₀ : MulAut V)⁻¹ * t ∈ centralizer (L : Set (MulAut V)) := by
    have h := (Subgroup.centralizer (L : Set (MulAut V))).inv_mem ht0c
    rwa [mul_inv_rev, ht₀inv, htinv] at h
  exact ⟨t, htA, t₀, ht1, ht₀1, hαt, ht0c, ht0cinv⟩

private theorem false_of_outer [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L A : Subgroup (MulAut V)} (hL : IsSimpleGroup ↥L) (hZ : center ↥L = ⊥)
    (hX : L2AutFacts ↥L) (hAL : A ≤ normalizer (L : Set (MulAut V)))
    (hA4 : Nat.card A = 4) (hA2 : ∀ a ∈ A, a * a = 1) (hAq : IsQuadratic A)
    (hAC : A ⊓ centralizer (L : Set (MulAut V)) = ⊥) (hfix : fixV L = ⊥)
    {t : MulAut V} (htA : t ∈ A) (ht1 : t ≠ 1) {t₀ : ↥L}
    (hαt : conjAct L ⟨t, hAL htA⟩ = MulAut.conj t₀)
    {u : MulAut V} (huA : u ∈ A) (hu1 : u ≠ 1) (hut : u ≠ t)
    (hnot : conjAct L ⟨u, hAL huA⟩ ∉ (MulAut.conj : ↥L →* MulAut ↥L).range) : False := by
  classical
  have htt : t * t = 1 := hA2 t htA
  have huu : u * u = 1 := hA2 u huA
  let E : Subgroup (MulAut V) := Subgroup.closure {t, u}
  have htE : t ∈ E := Subgroup.subset_closure (by simp)
  have huE : u ∈ E := Subgroup.subset_closure (by simp)
  have hEA : E ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact htA
    · exact huA
  have hquadE : IsQuadratic E := by
    have hcomm : commV E ≤ commV A := by
      rw [FixVLat.commV_le_iff]
      intro x hx v
      exact Subgroup.subset_closure ⟨x, hEA hx, v, rfl⟩
    exact hcomm.trans (hAq.trans (fixV_anti hEA))
  let Yt : Subgroup (MulAut V) := quadY (E ⊔ L) E t
  let Yu : Subgroup (MulAut V) := quadY (E ⊔ L) E u
  have hYt : ∀ y ∈ Yt, ∀ w ∈ commV (Subgroup.zpowers t), y w = w :=
    fixes_commV_quadY hquadE htE
  have hYu : ∀ y ∈ Yu, ∀ w ∈ commV (Subgroup.zpowers u), y w = w :=
    fixes_commV_quadY hquadE huE
  have htu : t * u = u * t := commute_of_card_four hA4 htA huA
  have htu_fix : ∀ v : V, u (t v * v⁻¹) = t v * v⁻¹ :=
    apply_commV_eq_of_isQuadratic hquadE htE huE
  have hut_fix : ∀ v : V, t (u v * v⁻¹) = u v * v⁻¹ :=
    apply_commV_eq_of_isQuadratic hquadE huE htE
  have hE_le_Yt : E ≤ Yt := by
    intro x hx
    refine Subgroup.mem_iSup_of_mem (1 : MulAut V) ?_
    refine Subgroup.mem_iSup_of_mem (by simp) ?_
    refine Subgroup.mem_iSup_of_mem (by simp) ?_
    simpa using Subgroup.mem_map_of_mem (MulAut.conj (1 : MulAut V)).toMonoidHom hx
  have htN : t ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAL htA
  have huN : u ∈ Subgroup.normalizer (L : Set (MulAut V)) := hAL huA
  have hαt_range : conjAct L ⟨t, htN⟩ ∈ (MulAut.conj : ↥L →* MulAut ↥L).range :=
    ⟨t₀, hαt.symm⟩
  have hαt_ne : conjAct L ⟨t, htN⟩ ≠ 1 := by
    intro h1
    have hcent : t ∈ centralizer (L : Set (MulAut V)) :=
      (AutOn.conjAct_eq_one_iff (V := L) ⟨t, htN⟩).1 h1
    have hmem : t ∈ A ⊓ centralizer (L : Set (MulAut V)) := ⟨htA, hcent⟩
    rw [hAC] at hmem
    exact ht1 (Subgroup.mem_bot.mp hmem)
  have hαt_sq : conjAct L ⟨t, htN⟩ * conjAct L ⟨t, htN⟩ = 1 := by
    have hsqN : (⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set (MulAut V)))) *
        ⟨t, htN⟩ = 1 := Subtype.ext htt
    rw [← map_mul, hsqN, map_one]
  have hαu_sq : conjAct L ⟨u, huN⟩ * conjAct L ⟨u, huN⟩ = 1 := by
    have hsqN : (⟨u, huN⟩ : ↥(Subgroup.normalizer (L : Set (MulAut V)))) *
        ⟨u, huN⟩ = 1 := Subtype.ext huu
    rw [← map_mul, hsqN, map_one]
  have htuN : (⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set (MulAut V)))) * ⟨u, huN⟩ =
      ⟨u, huN⟩ * ⟨t, htN⟩ := Subtype.ext htu
  have hcommα : conjAct L ⟨t, htN⟩ * conjAct L ⟨u, huN⟩ =
      conjAct L ⟨u, huN⟩ * conjAct L ⟨t, htN⟩ := by
    simpa only [← map_mul] using congrArg (conjAct L) htuN
  have hαt_range' : conjAct L ⟨t, hAL htA⟩ ∈
      (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rwa [show (⟨t, htN⟩ : ↥(Subgroup.normalizer (L : Set (MulAut V)))) =
      ⟨t, hAL htA⟩ from Subtype.ext rfl] at hαt_range
  rcases hX.outer (conjAct L ⟨t, htN⟩) (conjAct L ⟨u, huN⟩) hαt_range
    (by rwa [show (⟨u, huN⟩ : ↥(Subgroup.normalizer (L : Set (MulAut V)))) =
      ⟨u, hAL huA⟩ from Subtype.ext rfl]) hαt_sq hαt_ne hαu_sq hcommα with hII | hIII
  · obtain ⟨τ, hτL, hτodd, htτ, hgen2⟩ :=
      exists_parrott_of_conjAct hL hZ (hAL htA) (hAL huA) htt huu htu hII.1
    have hgenY : L ≤ Yt ⊔ Yu :=
      le_quadY_sup_of_conjAct hL hZ (hAL htA) (hAL huA) htt huu htu hII.2
    have hgen1 : L ≤ Yt ⊔ Subgroup.zpowers τ := by
      have hle : Subgroup.closure ({t, u, τ} : Set (MulAut V)) ≤
          Yt ⊔ Subgroup.zpowers τ := by
        refine (Subgroup.closure_le (Yt ⊔ Subgroup.zpowers τ)).mpr ?_
        intro x hx
        rcases hx with h | h | h
        · rw [h]; exact Subgroup.mem_sup_left (hE_le_Yt htE)
        · rw [h]; exact Subgroup.mem_sup_left (hE_le_Yt huE)
        · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
      exact hgen2.trans hle
    have hle : commV (Subgroup.zpowers u) ≤ commV (Subgroup.zpowers t) :=
      commV_le_of_parrott hV hfix (L := L) (Y := Yt) (by rw [pow_two]; exact htt)
        (by rw [pow_two]; exact huu) htu_fix hut_fix hτodd htτ hYt hgen1 hgen2
    exact not_commV_le_of_sup hfix hu1 hYt hYu hgenY hle
  · obtain ⟨p, U, U₀, hp, hp2, hUL, hUne, hcomm, hexp, huU, hU₀U, hU₀u,
      hU₀quad, hhyp⟩ :=
      exists_of_l2CaseIII_conjAct hL hZ (hAL htA) (hAL huA) htt huu htu hIII
    have hU₀fix : ∀ x ∈ U₀, ∀ w ∈ commV (Subgroup.zpowers u), x w = w :=
      fun x hx => fixes_commV_quadY hquadE huE x (hU₀quad hx)
    have hhyp' : ∀ H : Subgroup (MulAut V), H ≤ U → H.relIndex U = p →
        ∃ s : MulAut V, (∀ x ∈ U, s * x * s⁻¹ ∈ U) ∧
          ¬ U₀ ≤ H.map (MulAut.conj s).toMonoidHom ∧
          (H.map (MulAut.conj s).toMonoidHom).map (MulAut.conj u).toMonoidHom ≠
            H.map (MulAut.conj s).toMonoidHom := by
      intro H hH hrel
      obtain ⟨s, -, hsU, hsH, hsuH⟩ := hhyp H hH hrel
      exact ⟨s, hsU, hsH, hsuH⟩
    exact hUne (eq_bot_of_hyperplanes hV hp hp2 hcomm hexp huU hU₀U hU₀u hU₀fix hhyp')

private theorem false_of_inner [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L A : Subgroup (MulAut V)} (hL : IsSimpleGroup ↥L) (hZ : center ↥L = ⊥)
    (hAL : A ≤ normalizer (L : Set (MulAut V))) (hA4 : Nat.card A = 4)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAq : IsQuadratic A)
    (hAC : A ⊓ centralizer (L : Set (MulAut V)) = ⊥) (hfix : fixV L = ⊥)
    {t : MulAut V} (htA : t ∈ A) (ht1 : t ≠ 1) {t₀ : ↥L}
    (hαt : conjAct L ⟨t, hAL htA⟩ = MulAut.conj t₀) (ht₀1 : (t₀ : MulAut V) ≠ 1)
    (ht0c : (t₀ : MulAut V)⁻¹ * t ∈ centralizer (L : Set (MulAut V)))
    {u : MulAut V} (huA : u ∈ A) (hu1 : u ≠ 1) (hut : u ≠ t) {u₀ : ↥L}
    (hαu : conjAct L ⟨u, hAL huA⟩ = MulAut.conj u₀) (hu₀1 : (u₀ : MulAut V) ≠ 1)
    (hI : L2InnerFacts ↥L) : False := by
  classical
  have htt : t * t = 1 := hA2 t htA
  have huu : u * u = 1 := hA2 u huA
  let E : Subgroup (MulAut V) := Subgroup.closure {t, u}
  have htE : t ∈ E := Subgroup.subset_closure (by simp)
  have huE : u ∈ E := Subgroup.subset_closure (by simp)
  have hEA : E ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact htA
    · exact huA
  have hquadE : IsQuadratic E := by
    have hcomm : commV E ≤ commV A := by
      rw [FixVLat.commV_le_iff]
      intro x hx v
      exact Subgroup.subset_closure ⟨x, hEA hx, v, rfl⟩
    exact hcomm.trans (hAq.trans (fixV_anti hEA))
  let Yt : Subgroup (MulAut V) := quadY (E ⊔ L) E t
  let Yu : Subgroup (MulAut V) := quadY (E ⊔ L) E u
  have hYt : ∀ y ∈ Yt, ∀ w ∈ commV (Subgroup.zpowers t), y w = w :=
    fixes_commV_quadY hquadE htE
  have hYu : ∀ y ∈ Yu, ∀ w ∈ commV (Subgroup.zpowers u), y w = w :=
    fixes_commV_quadY hquadE huE
  have htu : t * u = u * t := commute_of_card_four hA4 htA huA
  have htu_fix : ∀ v : V, u (t v * v⁻¹) = t v * v⁻¹ :=
    apply_commV_eq_of_isQuadratic hquadE htE huE
  have hut_fix : ∀ v : V, t (u v * v⁻¹) = u v * v⁻¹ :=
    apply_commV_eq_of_isQuadratic hquadE huE htE
  have hE_le_Yt : E ≤ Yt := by
    intro x hx
    refine Subgroup.mem_iSup_of_mem (1 : MulAut V) ?_
    refine Subgroup.mem_iSup_of_mem (by simp) ?_
    refine Subgroup.mem_iSup_of_mem (by simp) ?_
    simpa using Subgroup.mem_map_of_mem (MulAut.conj (1 : MulAut V)).toMonoidHom hx
  have hE_le_Yu : E ≤ Yu := by
    intro x hx
    refine Subgroup.mem_iSup_of_mem (1 : MulAut V) ?_
    refine Subgroup.mem_iSup_of_mem (by simp) ?_
    refine Subgroup.mem_iSup_of_mem (by simp) ?_
    simpa using Subgroup.mem_map_of_mem (MulAut.conj (1 : MulAut V)).toMonoidHom hx
  have hinj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hcent : (z : ↥L) ∈ center ↥L := mem_center_of_conj_eq_one hz
    rw [hZ] at hcent
    exact Subgroup.mem_bot.mp hcent
  have ht₀sq : t₀ * t₀ = 1 := by
    have hsqN : (⟨t, hAL htA⟩ : ↥(Subgroup.normalizer (L : Set (MulAut V)))) * ⟨t, hAL htA⟩ = 1 :=
      Subtype.ext (hA2 t htA)
    have hconj : MulAut.conj t₀ * MulAut.conj t₀ = 1 := by
      rw [← hαt, ← map_mul, hsqN, map_one]
    exact sq_eq_one_of_conj_sq_eq_one hZ hconj
  have hu₀sq : u₀ * u₀ = 1 := by
    have hsqN : (⟨u, hAL huA⟩ : ↥(Subgroup.normalizer (L : Set (MulAut V)))) * ⟨u, hAL huA⟩ = 1 :=
      Subtype.ext (hA2 u huA)
    have hconj : MulAut.conj u₀ * MulAut.conj u₀ = 1 := by
      rw [← hαu, ← map_mul, hsqN, map_one]
    exact sq_eq_one_of_conj_sq_eq_one hZ hconj
  have ht₀1' : t₀ ≠ 1 := fun h => ht₀1 (by rw [h]; rfl)
  have hu₀1' : u₀ ≠ 1 := fun h => hu₀1 (by rw [h]; rfl)
  have htuN : (⟨t, hAL htA⟩ : ↥(Subgroup.normalizer (L : Set (MulAut V)))) * ⟨u, hAL huA⟩ =
      ⟨u, hAL huA⟩ * ⟨t, hAL htA⟩ := Subtype.ext htu
  have hconj_eq : MulAut.conj (t₀ * u₀) = MulAut.conj (u₀ * t₀) := by
    calc MulAut.conj (t₀ * u₀) = MulAut.conj t₀ * MulAut.conj u₀ := map_mul _ _ _
      _ = conjAct L ⟨t, hAL htA⟩ * conjAct L ⟨u, hAL huA⟩ := by rw [hαt, hαu]
      _ = conjAct L ((⟨t, hAL htA⟩ :
          ↥(Subgroup.normalizer (L : Set (MulAut V)))) * ⟨u, hAL huA⟩) :=
        (map_mul _ _ _).symm
      _ = conjAct L ((⟨u, hAL huA⟩ :
          ↥(Subgroup.normalizer (L : Set (MulAut V)))) * ⟨t, hAL htA⟩) := by
        rw [htuN]
      _ = conjAct L ⟨u, hAL huA⟩ * conjAct L ⟨t, hAL htA⟩ := map_mul _ _ _
      _ = MulAut.conj u₀ * MulAut.conj t₀ := by rw [hαu, hαt]
      _ = MulAut.conj (u₀ * t₀) := (map_mul _ _ _).symm
  have ht₀u₀_comm : t₀ * u₀ = u₀ * t₀ := by
    have hd : MulAut.conj ((t₀ * u₀) * (u₀ * t₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, hconj_eq, mul_inv_cancel]
    have hcent : (t₀ * u₀) * (u₀ * t₀)⁻¹ ∈ center ↥L :=
      mem_center_of_conj_eq_one hd
    rw [hZ, Subgroup.mem_bot, mul_inv_eq_one] at hcent
    exact hcent
  have ht₀u₀ : t₀ ≠ u₀ := by
    intro h
    have hαeq : conjAct L ⟨t, hAL htA⟩ = conjAct L ⟨u, hAL huA⟩ := by
      rw [hαt, hαu, h]
    have hz1 : conjAct L ⟨t * u, hAL (A.mul_mem htA huA)⟩ = 1 := by
      have hprod : (⟨t * u, hAL (A.mul_mem htA huA)⟩ :
          ↥(Subgroup.normalizer (L : Set (MulAut V)))) =
          ⟨t, hAL htA⟩ * ⟨u, hAL huA⟩ := Subtype.ext rfl
      have huuN : (⟨u, hAL huA⟩ : ↥(Subgroup.normalizer (L : Set (MulAut V)))) *
          ⟨u, hAL huA⟩ = 1 := Subtype.ext huu
      rw [hprod, map_mul, hαeq, ← map_mul, huuN, map_one]
    have hcent : t * u ∈ centralizer (L : Set (MulAut V)) :=
      (AutOn.conjAct_eq_one_iff (V := L) ⟨t * u, hAL (A.mul_mem htA huA)⟩).1 hz1
    have hbot : t * u ∈ A ⊓ centralizer (L : Set (MulAut V)) :=
      ⟨A.mul_mem htA huA, hcent⟩
    rw [hAC] at hbot
    have htu1 : t * u = 1 := Subgroup.mem_bot.mp hbot
    have ht_eq_u : t = u := by
      calc t = t * (u * u) := by rw [huu, mul_one]
        _ = (t * u) * u := by group
        _ = u := by rw [htu1, one_mul]
    exact hut ht_eq_u.symm
  have hparrott : ParrottGen (MulAut.conj : ↥L →* MulAut ↥L).range
      (conjAct L ⟨t, hAL htA⟩) (conjAct L ⟨u, hAL huA⟩) := by
    have hgen := hI.gen t₀ u₀ ht₀sq ht₀1' hu₀sq hu₀1' ht₀u₀_comm ht₀u₀
    have hmap := ParrottGen.map (f := (MulAut.conj : ↥L →* MulAut ↥L)) hinj hgen
    simpa only [Subgroup.map_top, ← hαt, ← hαu] using hmap
  obtain ⟨τ, hτL, hτodd, htτ, hgen2⟩ :=
    exists_parrott_of_conjAct hL hZ (hAL htA) (hAL huA) htt huu htu hparrott
  have hgen1 : L ≤ Yt ⊔ Subgroup.zpowers τ := by
    have hle : Subgroup.closure ({t, u, τ} : Set (MulAut V)) ≤
        Yt ⊔ Subgroup.zpowers τ := by
      refine (Subgroup.closure_le (Yt ⊔ Subgroup.zpowers τ)).mpr ?_
      intro x hx
      rcases hx with h | h | h
      · rw [h]; exact Subgroup.mem_sup_left (hE_le_Yt htE)
      · rw [h]; exact Subgroup.mem_sup_left (hE_le_Yt huE)
      · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
    exact hgen2.trans hle
  have hle_tu : commV (Subgroup.zpowers u) ≤ commV (Subgroup.zpowers t) :=
    commV_le_of_parrott hV hfix (L := L) (Y := Yt) (by rw [pow_two]; exact htt)
      (by rw [pow_two]; exact huu) htu_fix hut_fix hτodd htτ hYt hgen1 hgen2
  have hparrott' : ParrottGen (MulAut.conj : ↥L →* MulAut ↥L).range
      (conjAct L ⟨u, hAL huA⟩) (conjAct L ⟨t, hAL htA⟩) := by
    have hgen := hI.gen u₀ t₀ hu₀sq hu₀1' ht₀sq ht₀1' ht₀u₀_comm.symm ht₀u₀.symm
    have hmap := ParrottGen.map (f := (MulAut.conj : ↥L →* MulAut ↥L)) hinj hgen
    simpa only [Subgroup.map_top, ← hαu, ← hαt] using hmap
  obtain ⟨τ', hτ'L, hτ'odd, huτ', hgen2'⟩ :=
    exists_parrott_of_conjAct hL hZ (hAL huA) (hAL htA) huu htt htu.symm hparrott'
  have hgen1' : L ≤ Yu ⊔ Subgroup.zpowers τ' := by
    have hle : Subgroup.closure ({u, t, τ'} : Set (MulAut V)) ≤
        Yu ⊔ Subgroup.zpowers τ' := by
      refine (Subgroup.closure_le (Yu ⊔ Subgroup.zpowers τ')).mpr ?_
      intro x hx
      rcases hx with h | h | h
      · rw [h]; exact Subgroup.mem_sup_left (hE_le_Yu huE)
      · rw [h]; exact Subgroup.mem_sup_left (hE_le_Yu htE)
      · rw [h]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ')
    exact hgen2'.trans hle
  have hle_ut : commV (Subgroup.zpowers t) ≤ commV (Subgroup.zpowers u) :=
    commV_le_of_parrott hV hfix (L := L) (Y := Yu) (by rw [pow_two]; exact huu)
      (by rw [pow_two]; exact htt) hut_fix htu_fix hτ'odd huτ' hYu hgen1' hgen2'
  have hW : commV (Subgroup.zpowers t) = commV (Subgroup.zpowers u) :=
    le_antisymm hle_ut hle_tu
  let C1 : Subgroup ↥L := Subgroup.centralizer ({t₀} : Set ↥L)
  let C2 : Subgroup ↥L := Subgroup.centralizer ({u₀} : Set ↥L)
  have hcent : C1 ⊔ C2 = ⊤ :=
    hI.cent t₀ u₀ ht₀sq ht₀1' hu₀sq hu₀1' ht₀u₀_comm ht₀u₀
  let S : Subgroup (MulAut V) := L ⊓ stabSub (commV (Subgroup.zpowers t))
  have hC1 : C1.map L.subtype ≤ S := by
    rintro x ⟨c, hc, rfl⟩
    refine ⟨c.2, ?_⟩
    have hc' : t₀ * c = c * t₀ := (Subgroup.mem_centralizer_iff.mp hc) t₀ rfl
    have hc'' : (t₀ : MulAut V) * (c : MulAut V) =
        (c : MulAut V) * (t₀ : MulAut V) :=
      congrArg (fun z : ↥L => (z : MulAut V)) hc'
    have hct : Commute (c : MulAut V) t := by
      have hc1 : Commute (t₀ : MulAut V) (c : MulAut V) := hc''
      have hc2 : Commute ((t₀ : MulAut V)⁻¹ * t) (c : MulAut V) :=
        ((Subgroup.mem_centralizer_iff.mp ht0c) (c : MulAut V) c.2).symm
      have hprod : Commute ((t₀ : MulAut V) * ((t₀ : MulAut V)⁻¹ * t))
          (c : MulAut V) := hc1.mul_left hc2
      rw [show t = (t₀ : MulAut V) * ((t₀ : MulAut V)⁻¹ * t) from by group]
      exact hprod.symm
    change (c : MulAut V) ∈ stabSub (commV (Subgroup.zpowers t))
    rw [mem_stabSub]
    intro w
    constructor
    · intro hw
      have hcinv : Commute (c : MulAut V)⁻¹ t := hct.inv_left
      have hmem := apply_mem_commV_zpowers_of_commute hcinv.eq hw
      simpa using hmem
    · intro hw
      exact apply_mem_commV_zpowers_of_commute hct.eq hw
  have hu₀N : (u₀ : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
    L.le_normalizer u₀.2
  have hαu₀ : conjAct L ⟨(u₀ : MulAut V), hu₀N⟩ = MulAut.conj u₀ :=
    conjAct_conj_of_mem u₀.2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hu₀inv : (u₀ : MulAut V)⁻¹ = (u₀ : MulAut V) :=
    inv_eq_of_mul_eq_one_right (congrArg (fun z : ↥L => (z : MulAut V)) hu₀sq)
  have hu0c : u * (u₀ : MulAut V)⁻¹ ∈ centralizer (L : Set (MulAut V)) := by
    have hNmul : u * (u₀ : MulAut V)⁻¹ ∈
        Subgroup.normalizer (L : Set (MulAut V)) :=
      (Subgroup.normalizer (L : Set (MulAut V))).mul_mem (hAL huA)
        ((Subgroup.normalizer (L : Set (MulAut V))).inv_mem hu₀N)
    let z : ↥(Subgroup.normalizer (L : Set (MulAut V))) :=
      ⟨u * (u₀ : MulAut V)⁻¹, hNmul⟩
    have hz : conjAct L z = 1 := by
      have hz_eq : z = ⟨u, hAL huA⟩ * ⟨(u₀ : MulAut V), hu₀N⟩⁻¹ := Subtype.ext rfl
      rw [hz_eq, map_mul, map_inv, hαu, hαu₀]
      simp
    exact (AutOn.conjAct_eq_one_iff z).1 hz
  have hu0c_inv : (u₀ : MulAut V)⁻¹ * u ∈ centralizer (L : Set (MulAut V)) := by
    have h := (Subgroup.centralizer (L : Set (MulAut V))).inv_mem hu0c
    rwa [mul_inv_rev, hu₀inv, huinv] at h
  have hC2 : C2.map L.subtype ≤ S := by
    rintro x ⟨c, hc, rfl⟩
    refine ⟨c.2, ?_⟩
    have hc' : u₀ * c = c * u₀ := (Subgroup.mem_centralizer_iff.mp hc) u₀ rfl
    have hc'' : (u₀ : MulAut V) * (c : MulAut V) =
        (c : MulAut V) * (u₀ : MulAut V) :=
      congrArg (fun z : ↥L => (z : MulAut V)) hc'
    have hcut : Commute (c : MulAut V) u := by
      have hc1 : Commute (u₀ : MulAut V) (c : MulAut V) := hc''
      have hc2 : Commute ((u₀ : MulAut V)⁻¹ * u) (c : MulAut V) :=
        ((Subgroup.mem_centralizer_iff.mp hu0c_inv) (c : MulAut V) c.2).symm
      have hprod : Commute ((u₀ : MulAut V) * ((u₀ : MulAut V)⁻¹ * u))
          (c : MulAut V) := hc1.mul_left hc2
      rw [show u = (u₀ : MulAut V) * ((u₀ : MulAut V)⁻¹ * u) from by group]
      exact hprod.symm
    have hstab : (c : MulAut V) ∈ stabSub (commV (Subgroup.zpowers u)) := by
      rw [mem_stabSub]
      intro w
      constructor
      · intro hw
        have hcinv : Commute (c : MulAut V)⁻¹ u := hcut.inv_left
        have hmem := apply_mem_commV_zpowers_of_commute hcinv.eq hw
        simpa using hmem
      · intro hw
        exact apply_mem_commV_zpowers_of_commute hcut.eq hw
    rw [hW]
    exact hstab
  have hLgen : L = C1.map L.subtype ⊔ C2.map L.subtype := by
    rw [← Subgroup.map_sup, hcent, Subgroup.map_top, Subgroup.range_subtype]
  have hS : L ≤ S := by
    rw [hLgen]
    exact sup_le hC1 hC2
  have hstab : ∀ l ∈ L, ∀ w ∈ commV (Subgroup.zpowers t), l w ∈ commV (Subgroup.zpowers t) := by
    intro l hl w hw
    exact (mem_stabSub.mp (hS hl).2 w).mpr hw
  exact false_of_stab_commV hV hL hZ hfix htt t₀.2 ht₀1 ht0c hstab

theorem inner_of_l2AutFacts [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)}
    (hL : IsSimpleGroup ↥L) (hZ : center ↥L = ⊥) (hX : L2AutFacts ↥L)
    (hAL : A ≤ normalizer (L : Set (MulAut V))) (hA4 : Nat.card A = 4)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAq : IsQuadratic A)
    (hAC : A ⊓ centralizer (L : Set (MulAut V)) = ⊥) (hfix : fixV L = ⊥) :
    ∀ a ∈ A, ∃ l ∈ L, a * l⁻¹ ∈ centralizer (L : Set (MulAut V)) := by
  classical
  obtain ⟨t, htA, t₀, ht1, ht₀1, hαt, ht0c, -⟩ :=
    exists_foote_data hZ hX hAL hA4 hA2 hAC
  intro a haA
  by_cases ha1 : a = 1
  · refine ⟨1, L.one_mem, ?_⟩
    simp [ha1]
  by_cases hat : a = t
  · refine ⟨(t₀ : MulAut V), t₀.2, ?_⟩
    rw [hat]
    exact ht0c
  · have haInn : conjAct L ⟨a, hAL haA⟩ ∈
        (MulAut.conj : ↥L →* MulAut ↥L).range := by
      by_contra hnot
      exact false_of_outer hV hL hZ hX hAL hA4 hA2 hAq hAC hfix htA ht1 hαt
        haA ha1 hat hnot
    obtain ⟨a₀, ha₀⟩ := haInn
    refine ⟨(a₀ : MulAut V), a₀.2, ?_⟩
    have ha₀N : (a₀ : MulAut V) ∈ Subgroup.normalizer (L : Set (MulAut V)) :=
      L.le_normalizer a₀.2
    have hαa : conjAct L ⟨a, hAL haA⟩ = MulAut.conj a₀ := ha₀.symm
    have hαa₀ : conjAct L ⟨(a₀ : MulAut V), ha₀N⟩ = MulAut.conj a₀ :=
      conjAct_conj_of_mem a₀.2
    have hNmul : a * (a₀ : MulAut V)⁻¹ ∈
        Subgroup.normalizer (L : Set (MulAut V)) :=
      (Subgroup.normalizer (L : Set (MulAut V))).mul_mem (hAL haA)
        ((Subgroup.normalizer (L : Set (MulAut V))).inv_mem ha₀N)
    let z : ↥(Subgroup.normalizer (L : Set (MulAut V))) :=
      ⟨a * (a₀ : MulAut V)⁻¹, hNmul⟩
    have hz : conjAct L z = 1 := by
      have hz_eq : z = ⟨a, hAL haA⟩ * ⟨(a₀ : MulAut V), ha₀N⟩⁻¹ := Subtype.ext rfl
      rw [hz_eq, map_mul, map_inv, hαa, hαa₀]
      simp
    exact (AutOn.conjAct_eq_one_iff z).1 hz

theorem false_of_l2Facts [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L A : Subgroup (MulAut V)}
    (hL : IsSimpleGroup ↥L) (hZ : center ↥L = ⊥) (hX : L2AutFacts ↥L) (hI : L2InnerFacts ↥L)
    (hAL : A ≤ normalizer (L : Set (MulAut V))) (hA4 : Nat.card A = 4)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAq : IsQuadratic A)
    (hAC : A ⊓ centralizer (L : Set (MulAut V)) = ⊥) (hfix : fixV L = ⊥) : False := by
  classical
  obtain ⟨t, htA, t₀, ht1, ht₀1, hαt, ht0c, ht0cinv⟩ :=
    exists_foote_data hZ hX hAL hA4 hA2 hAC
  have : Fintype ↥A := Fintype.ofFinite _
  have hcardA : Fintype.card ↥A = 4 := by
    rw [← Nat.card_eq_fintype_card, hA4]
  let s : Finset ↥A := {(⟨1, A.one_mem⟩ : ↥A), ⟨t, htA⟩}
  have hs_card : s.card = 2 := by
    rw [Finset.card_pair]
    intro h
    exact ht1 (congrArg Subtype.val h).symm
  have hssub : s ⊂ Finset.univ := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_univ _, ?_⟩
    intro h
    have hcard := congrArg Finset.card h
    rw [hs_card] at hcard
    have huniv : (Finset.univ : Finset ↥A).card = 4 := hcardA
    rw [huniv] at hcard
    norm_num at hcard
  obtain ⟨u, -, hu_notin⟩ := Finset.exists_of_ssubset hssub
  have huA : (u : MulAut V) ∈ A := u.2
  have hu1 : (u : MulAut V) ≠ 1 := by
    intro h
    apply hu_notin
    rw [Finset.mem_insert, Finset.mem_singleton]
    left
    exact Subtype.ext h
  have hut : (u : MulAut V) ≠ t := by
    intro h
    apply hu_notin
    rw [Finset.mem_insert, Finset.mem_singleton]
    right
    exact Subtype.ext h
  have huInn : conjAct L ⟨(u : MulAut V), hAL huA⟩ ∈
      (MulAut.conj : ↥L →* MulAut ↥L).range := by
    by_contra hnot
    exact false_of_outer hV hL hZ hX hAL hA4 hA2 hAq hAC hfix htA ht1 hαt
      huA hu1 hut hnot
  obtain ⟨u₀, hu₀⟩ := huInn
  have hαu : conjAct L ⟨(u : MulAut V), hAL huA⟩ = MulAut.conj u₀ := hu₀.symm
  have hu₀1 : (u₀ : MulAut V) ≠ 1 := by
    intro h
    have hαu1 : conjAct L ⟨(u : MulAut V), hAL huA⟩ = 1 := by
      rw [hαu, show u₀ = 1 from Subtype.ext h, map_one]
    have hcent : (u : MulAut V) ∈ centralizer (L : Set (MulAut V)) :=
      (AutOn.conjAct_eq_one_iff (V := L) ⟨(u : MulAut V), hAL huA⟩).1 hαu1
    have hbot : (u : MulAut V) ∈ A ⊓ centralizer (L : Set (MulAut V)) :=
      ⟨huA, hcent⟩
    rw [hAC] at hbot
    exact hu1 (Subgroup.mem_bot.mp hbot)
  exact false_of_inner hV hL hZ hAL hA4 hA2 hAq hAC hfix htA ht1 hαt ht₀1 ht0cinv
    huA hu1 hut hαu hu₀1 hI

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
