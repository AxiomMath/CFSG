module

public import CFSG.Quasithin.MS93.FFStatement
public import CFSG.Quasithin.Background.InternalSecB5
public import CFSG.Quasithin.Background.S1549DGen

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

namespace FFHyp

theorem conj_mem (h : FFHyp X K) {x k : MulAut V} (hx : x ∈ X) (hk : k ∈ K) :
    x * k * x⁻¹ ∈ K :=
  (Subgroup.mem_normalizer_iff.mp (h.le_normalizer hx) k).mp hk

theorem commV_inv (h : FFHyp X K) {x : MulAut V} (hx : x ∈ X) {v : V} (hv : v ∈ commV K) :
    x v ∈ commV K := by
  have hle : commV K ≤ (commV K).comap x.toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨k, hk, w, rfl⟩
    show x (k w * w⁻¹) ∈ commV K
    have e : x (k w * w⁻¹) = (x * k * x⁻¹) (x w) * (x w)⁻¹ := by
      simp [MulAut.mul_apply]
    rw [e]
    exact Subgroup.subset_closure ⟨_, h.conj_mem hx hk, x w, rfl⟩
  exact hle hv

theorem fixV_inv (h : FFHyp X K) {x : MulAut V} (hx : x ∈ X) {v : V} (hv : v ∈ fixV K) :
    x v ∈ fixV K :=
  B1Red.fixV_inv_of_normalizes (fun _ hb _ hk => h.conj_mem hb hk) x hx v hv

theorem commV_sup_fixV (hV : ∀ v : V, v ^ 2 = 1) (h : FFHyp X K) : commV K ⊔ fixV K = ⊤ := by
  obtain ⟨T, hT, hgen⟩ := h.gen
  have h1 : fixV T ≤ commV K ⊔ fixV K := S1549D.fixV_le_commV_sup_fixV hV hT
  have hinv : ∀ x ∈ X, ∀ v ∈ commV K ⊔ fixV K, x v ∈ commV K ⊔ fixV K := by
    intro x hx v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hv
    rw [map_mul]
    exact Subgroup.mul_mem_sup (h.commV_inv hx ha) (h.fixV_inv hx hb)
  rw [eq_top_iff, ← hgen]
  refine iSup₂_le fun x hx => ?_
  rintro _ ⟨v, hv, rfl⟩
  exact hinv x hx v (h1 hv)

theorem fixV_eq_bot (hV : ∀ v : V, v ^ 2 = 1) (h : FFHyp X K) : fixV K = ⊥ := by
  by_contra hne
  set W := fixV K with hW
  have hWst : ∀ x ∈ X, x ∈ stabSub W := by
    intro x hx u
    refine ⟨fun hu => ?_, fun hu => h.fixV_inv hx hu⟩
    have := h.fixV_inv (X.inv_mem hx) hu
    simpa using this
  have hP : IsPGroup 2 ↥(autSub X W) := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hgX, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨e, he⟩ := h.two g hgX
    refine ⟨e, Subtype.ext ?_⟩
    show (resHom W g) ^ 2 ^ e = 1
    rw [← map_pow]
    ext u
    show ((g ^ 2 ^ e : stabSub W) : MulAut V) (u : V) = u
    rw [Subgroup.coe_pow]
    exact u.2 _ he
  have hV' : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hnt : Nontrivial ↥W := (Subgroup.nontrivial_iff_ne_bot W).2 hne
  obtain ⟨m, -, hm1, hmfix⟩ := B1.exists_fixed_ne_one hV' hP (M := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _) top_ne_bot
  have hmX : (m : V) ∈ fixV X := fun x hx => by
    have := hmfix (resHom W ⟨x, hWst x hx⟩) (mem_autSub.mpr ⟨⟨x, hWst x hx⟩, hx, rfl⟩)
    exact congrArg Subtype.val this
  rw [h.fix, Subgroup.mem_bot] at hmX
  exact hm1 (Subtype.ext hmX)

theorem commV_eq_top (hV : ∀ v : V, v ^ 2 = 1) (h : FFHyp X K) : commV K = ⊤ := by
  have := h.commV_sup_fixV hV
  rwa [h.fixV_eq_bot hV, sup_bot_eq] at this

theorem exists_offender (h : FFHyp X K) : ∃ A, IsFFStarOffender X A :=
  B6.exists_isFFStarOffender h.ff

theorem b51Hyp (h : FFHyp X K) : B51Hyp (ffJ X) K := by
  set J := ffJ X with hJ
  have hKo := B1Red.isQuasisimple_to_open h.quasisimple
  have hJX : J ≤ X := B6.ffJ_le _
  have hXJ : X ≤ Subgroup.normalizer (J : Set (MulAut V)) := B6.le_normalizer_ffJ _
  obtain ⟨A, hA⟩ := h.exists_offender
  have hAJ : A ≤ J := B6.le_ffJ hA
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.2.2.1.2
  have hKnil : ∀ P : Subgroup (MulAut V), K ≤ P → ¬ IsPGroup 2 ↥P := by
    intro P hKP hP
    have hnil := (hP.to_le hKP).isNilpotent
    have : Group.IsPerfect ↥K := ⟨hKo.1⟩
    have : Nontrivial ↥K := CFSG.ComponentClassification.Quasisimple.nontrivial hKo
    exact Group.IsPerfect.not_isNilpotent ↥K hnil
  have hKJ : K ≤ J := by
    by_contra hKJ
    have hcomm := B1Red.commute_of_normal_not_le hKo
      (fun n hn l hl => h.conj_mem (hJX hn) hl)
      (fun l hl n hn => (Subgroup.mem_normalizer_iff.mp (hXJ (h.le hl)) n).mp hn) hKJ
    apply hA.2.1
    rw [eq_bot_iff]
    intro a ha
    exact Subgroup.mem_bot.2
      (h.cent a (hJX (hAJ ha)) (fun k hk => hcomm a (hAJ ha) k hk) 1 (by simpa using hA2 a ha))
  have hQ : pCoreOf 2 J = ⊥ := by
    have hQ2 : IsPGroup 2 ↥(pCoreOf 2 J) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
    have hQle : pCoreOf 2 J ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
    have hnot : ¬ K ≤ pCoreOf 2 J := fun hle => hKnil _ hle hQ2
    have hcomm := B1Red.commute_of_normal_not_le hKo
      (fun n hn l hl => h.conj_mem (hJX (hQle hn)) hl)
      (fun l hl n hn => B1Red.conj_mem_pCoreOf (hKJ hl) hn) hnot
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨e, he⟩ := hQ2 ⟨q, hq⟩
    exact Subgroup.mem_bot.2 (h.cent q (hJX (hQle hq)) (fun k hk => hcomm q hq k hk) e
      (by simpa using congrArg Subtype.val he))
  have h2 : ∀ y ∈ J, ∃ e : ℕ, y ^ 2 ^ e ∈ K := fun y hy => h.two y (hJX hy)
  have hF : quasithinGenFitting J = K :=
    InternalSec.quasithinGenFitting_eq_of_two_pow hKJ (fun y hy l hl => h.conj_mem (hJX hy) hl)
      hKo h2 hQ
  have hZ : centerOf J ≤ K := by
    rintro z ⟨hzJ, hzc⟩
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
    have hzm : z ^ m = 1 := by
      refine h.cent _ (X.pow_mem (hJX hzJ) m) (fun l hl => ?_) k ?_
      · have h1 : Commute z l :=
          (Subgroup.mem_centralizer_iff.mp hzc l (hKJ hl)).symm
        exact (h1.pow_left m).eq
      · rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
    have hodd : Odd (orderOf z) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hzm)
    obtain ⟨e, he⟩ := h2 z hzJ
    exact InternalSec.mem_of_pow_mem_of_odd he hodd
  exact ⟨by rw [hF, sup_eq_left.2 hZ], h.quasisimple, h.sqtk, hKJ, hQ,
    (InternalSec.ffJ_ffJ _).symm⟩

end FFHyp

end CFSG.Quasithin.MS93
