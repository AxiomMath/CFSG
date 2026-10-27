module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.List.GetD

public section

namespace CFSG.StandardType.WeylE8Bound

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def reflect8 (i : Fin Tag.E8.rank) (v : Fin Tag.E8.rank → ℤ) : Fin Tag.E8.rank → ℤ :=
  reflect .E8 i v

@[expose] def e8RootCodes : List ℕ :=
  [37451721174229442, 36888771220808130, 36884373174297026, 36884338814558658, 36884338546123202,
   36884338544026050, 36884338544025922, 36884338544009666, 36884338544009665, 36884338544009538,
   36884338544009537, 36884338541912386, 36884338541912385, 36884338273476930, 36884338541896001,
   36884338273476929, 36884303913738562, 36884338273460545, 36884303913738561, 36879905867227458,
   36884338271363393, 36884303913722177, 36879905867227457, 36316955913806146, 36884338271363265,
   36884303911625025, 36879905867211073, 36316955913806145, 36884303911624897, 36884303643189569,
   36879905865113921, 36316955913789761, 36884303643189441, 36879905865113793, 36879905596678465,
   36316955911692609, 36884303641092289, 36879905596678337, 36316955911692481, 36879871236940097,
   36316955643257153, 36884303641075905, 36879905594581185, 36879871236939969, 36316955643257025,
   36316921283518785, 36884303641075904, 36879905594564801, 36879871234842817, 36316955641159873,
   36316921283518657, 36312523237007681, 36879905594564800, 36879871234826433, 36316955641143489,
   36879870966407361, 36316921281421505, 36312523237007553, 36879871234826432, 36316955641143488,
   36879870966390977, 36316921281405121, 36316921012986049, 36312523234910401, 36879870966390976,
   36316921281405120, 36879870964293825, 36316921012969665, 36312523234894017, 36312522966474945,
   36879870964293824, 36316921012969664, 36312523234894016, 36879870964293697, 36316921010872513,
   36312522966458561, 36312488606736577, 36879870964293696, 36879870964277440, 36316921010872512,
   36312522966458560, 36316921010872385, 36312522964361409, 36312488606720193, 36879870964277312,
   36316921010872384, 36316921010856128, 36312522964361408, 36312488606720192, 36312522964361281,
   36312488604623041, 36879870962180160, 36316921010856000, 36312522964361280, 36312522964345024,
   36312488604623040, 36312488604622913, 36312488336187585, 36879870693744704, 36316921008758848,
   36312522964344896, 36312488604622912, 36312488604606656, 36312488336187584, 36312488336187457,
   36879836334006336, 36316920740323392, 36312522962247744, 36312488604606528, 36312488336187456,
   36312488336171200, 36312488334090305, 36875438287495232, 36316886380585024, 36312522693812288,
   36312488602509376, 36312488336171072, 36312488334090304, 36312488334074048, 36312488334073921,
   35173255493918398, 35736205447339710, 35740603493850814, 35740637853589182, 35740638122024638,
   35740638124121790, 35740638124138174, 35740638124121918, 35740638124138302, 35740638124138175,
   35740638126235454, 35740638124138303, 35740638394670910, 35740638126235455, 35740672754409278,
   35740638394670911, 35740638126251839, 35745070800920382, 35740672754409279, 35740638394687295,
   36308020754341694, 35745070800920383, 35740672754425663, 35740638396784447, 36308020754341695,
   35745070800936767, 35740672756522815, 35740638396784575, 36308020754358079, 35745070803033919,
   35740673024958271, 35740672756522943, 36308020756455231, 35745071071469375, 35745070803034047,
   35740673024958399, 36308021024890687, 35745105431207743, 36308020756455359, 35745071071469503,
   35740673027055551, 36308055384629055, 36308021024890815, 35745105431207871, 35745071073566655,
   35740673027071935, 36312453431140159, 36308055384629183, 36308021026987967, 35745105433305023,
   35745071073583039, 35740673027071936, 36312453431140287, 36308055386726335, 35745105701740479,
   36308021027004351, 35745105433321407, 35745071073583040, 36312453433237439, 36308055655161791,
   36308055386742719, 35745105701756863, 36308021027004352, 35745105433321408, 36312453701672895,
   36312453433253823, 36308055655178175, 35745105703854015, 36308055386742720, 35745105701756864,
   36312488061411263, 36312453701689279, 36308055657275327, 35745105703854143, 36312453433253824,
   36308055655178176, 35745105703854016, 36312488061427647, 36312453703786431, 36308055657275455,
   36312453701689280, 36308055657275328, 35745105703870400, 35745105703854144, 36312488063524799,
   36312453703786559, 36312488061427648, 36312453703786432, 36308055657291712, 36308055657275456,
   35745105703870528, 36312488331960255, 36312488063524927, 36312488063524800, 36312453703802816,
   36312453703786560, 36308055657291840, 35745105705967680, 36312488331960383, 36312488331960256,
   36312488063541184, 36312488063524928, 36312453703802944, 36308055659388992, 35745105974403136,
   36312488334057535, 36312488331976640, 36312488331960384, 36312488063541312, 36312453705900096,
   36308055927824448, 35745140334141504, 36312488334073919, 36312488334073792, 36312488334057536,
   36312488331976768, 36312488065638464, 36312453974335552, 36308090287562816, 35749538380652608]

@[expose] def e8ReflCodes : List ℕ :=
  [72057594037927936, 564053776859393, 144399970211070466, 217019423297569539, 289360687074116612,
   361700864173737477, 434041037028656390, 506381209866406152, 578721382704613895,
   651061555576047370, 723401728414320649, 795741909775223564, 868082086908398603,
   940425536839945487, 1012762432617844238, 1085105878221262605, 1158283891804475410,
   1229787323459113233, 1303245712457536016, 1661849235145036566, 1446808954269341716,
   1520546606503564565, 1950645872720746003, 1375593599124051739, 1736168546160350232,
   1809906215390092313, 2239725089162926618, 1592896696438692631, 2026927833483057436,
   2099272370007908381, 2529085797561147678, 1882257387857583903, 2316292888589245728,
   2746106316142485025, 2890509546216891682, 2171618100550772259, 2605935071964242980,
   3179588758364561957, 2388638623427076902, 3253606807354420007, 2461266825378802728,
   2967635936221079854, 3541008164590660138, 3615023993316910891, 2678571017993725996,
   2824645565788009005, 3329336800411790889, 3902709028864274228, 4048782481442549808,
   3040273007298097457, 3114569211506208050, 3687659964881647923, 4264409893054985263,
   4410483345716163898, 3401973871571711547, 4483112634295269175, 3476551580553918520,
   4121419527034057529, 4700126611573979701, 3763673636250794806, 4844813498585660480,
   3838252444844309825, 3982657856762756670, 4555460589631323967, 5134174194233262140,
   4199671829746499901, 5350912159515822406, 4344640196046635847, 4917161458216682568,
   4989509271802299717, 5712330444906581314, 4634282362392758083, 5206522153864284228,
   5857293369483018829, 4778963837410496847, 5423269929187363664, 5497845439112891468,
   6146654060835784265, 6218994233672881230, 5068607107546633546, 5784689314106462283,
   5285345047394470485, 5929651168884185431, 6004225549584323416, 6653035270818844244,
   5574705738747236177, 5647045911584398422, 6291352033075027282, 6365926413775165523,
   6436031279356531293, 6510606789281210463, 7159416510515731291, 6081086948730295900,
   6725393070220924761, 6797733243058087006, 6872307657767019866, 6944648930233703013,
   7016996735228668007, 7665805356951560802, 6587468188427182947, 7231774280203984484,
   7306348694912917344, 7378688867750079590, 7451037767962619233, 7523377940917674349,
   8174141528557054313, 7093857034863012458, 7738155519900871531, 7812729904895977068,
   7885078805125293928, 7957418977962456174, 8029759184909594485, 17251443475844460656,
   7633155453906678129, 8244663113592500850, 8319111599859397491, 8391460016853184116,
   8463800221928420719, 8536140394758859126, 8608480567730599912, 8752878334607128696,
   8681384794346060153, 8825220710780271226, 8897840163866770299, 8970181427643317372,
   9042521604742872957, 9114861777597595777, 9187201950435802495, 9259542123307302531,
   9331882296111891326, 9404222477506347653, 9476562641821598080, 9548905005059441799,
   9621242996020774274, 9694425386209150602, 9765926623085561732, 9838263518863132808,
   10125932036000156045, 9983784978050091654, 10055287310209485707, 9911451415216950416,
   10415292727352724873, 10273145669468982926, 10344648014312739727, 10200812106569519244,
   10704653418771616145, 10562506377867204498, 10634009805243781011, 10490172797988410516,
   10994014127169837717, 10851870333461765014, 10924206142613066391, 10779533506386632344,
   11283379182276026265, 11427772589760222618, 11213852672712742555, 11068899661004448412,
   11645633113683239837, 11141516949444270238, 11717138740116691359, 11575553553915551904,
   11359939328104048545, 11502940698133568674, 12079674150812360099, 12150898319164089508,
   11937535893165876651, 12007061316237175974, 11793980365233168807, 11864924158103103656,
   12513714109603162537, 12656716574848494257, 12371858405171375013, 12441102353366296236,
   12228021427830566317, 12947478022540603054, 12299247774031458230, 13020094220057817271,
   13162816309738713514, 12875143415963693746, 12590010316940293043, 12734402637796848828,
   13453859232506885565, 12805630083410081455, 13598533028257707952, 13309190998622976184,
   13381524625929976258, 13096391526906575555, 13887900290809315780, 13241346806224043188,
   14104638204971695541, 13744626242165259966, 13815572208606035912, 13530714064480683977,
   14393998921976363979, 14032304706496414393, 13675395484116829114, 14538961846335622075,
   14251007452148319694, 14321671969031245263, 13965037680409952465, 14466633764149184703,
   14181775620023833024, 15045060477518664394, 15117400650357589185, 14757388691845207253,
   14828054278526846679, 14902069007691468485, 14972733524574394310, 14616099235952187600,
   14688439408791177671, 15623781860340648658, 15263776438769408731, 15336108970860661981,
   15408450243093388748, 15479114734557454038, 15551454907396444109, 15194820618774237400,
   16130163100037536217, 15770157653048349667, 15842497825769448403, 15914831453076448476,
   15987171625915438548, 16057836117379503838, 15701201858471124959, 16636551946473365728,
   16276538888450269674, 16348879035752508386, 16421219208591563738, 16493552840210242788,
   16564218460882986469, 16207873279395292902, 17217227187093497831, 16782920098433329271,
   16855260271154394857, 16927600443984833249, 16999940584886231787, 17072272573379439852,
   17142515363497242093, 16677364809014898414, 8135735065669791727]

@[expose] def decodeRoot (c : ℕ) (i : Fin Tag.E8.rank) : ℤ :=
  ((c / 128 ^ i.val % 128 : ℕ) : ℤ) - 64

@[expose] def decodeTable (c : ℕ) (i : Fin Tag.E8.rank) : ℕ :=
  c / 256 ^ i.val % 256

@[expose] def e8Root (k : Fin 240) : Fin Tag.E8.rank → ℤ :=
  fun i => decodeRoot (e8RootCodes.getD k.val 0) i

@[expose] def e8ReflIdxNat (k : Fin 240) (i : Fin Tag.E8.rank) : ℕ :=
  decodeTable (e8ReflCodes.getD k.val 0) i

theorem e8ReflIdxNat_lt : ∀ (k : Fin 240) (i : Fin Tag.E8.rank), e8ReflIdxNat k i < 240 := by
  decide +kernel

@[expose] def e8ReflIdx (k : Fin 240) (i : Fin Tag.E8.rank) : Fin 240 :=
  ⟨e8ReflIdxNat k i, e8ReflIdxNat_lt k i⟩

theorem e8Root_reflect : ∀ (k : Fin 240) (i j : Fin Tag.E8.rank),
    reflect8 i (e8Root k) j = e8Root (e8ReflIdx k i) j := by
  decide +kernel

@[expose] def e8Cartan : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ := Tag.cartan .E8

theorem e8Cartan_symm : ∀ i j : Fin Tag.E8.rank, e8Cartan i j = e8Cartan j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem e8Cartan_diag : ∀ i : Fin Tag.E8.rank, e8Cartan i i = 2 := by
  intro i
  fin_cases i <;> decide +kernel

@[expose] def e8Form (u v : Fin Tag.E8.rank → ℤ) : ℤ := dotProduct u (Matrix.mulVec e8Cartan v)

theorem dot_col_eq_mulVec : ∀ (i : Fin Tag.E8.rank) (u : Fin Tag.E8.rank → ℤ),
    dotProduct u (Matrix.col e8Cartan i) = (Matrix.mulVec e8Cartan u) i := by
  intro i u
  simp only [dotProduct, Matrix.col_apply, Matrix.mulVec]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e8Cartan_symm k i, mul_comm]

theorem e8Form_sub_sub_smul (i : Fin Tag.E8.rank) (u v : Fin Tag.E8.rank → ℤ) :
    e8Form (u - (∑ j, e8Cartan i j * u j) • Pi.single i 1)
         (v - (∑ j, e8Cartan i j * v j) • Pi.single i 1) = e8Form u v := by
  rw [show (∑ j, e8Cartan i j * u j) = (Matrix.mulVec e8Cartan u) i from rfl,
      show (∑ j, e8Cartan i j * v j) = (Matrix.mulVec e8Cartan v) i from rfl]
  simp only [e8Form]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, single_dotProduct, dotProduct_single,
    Pi.sub_apply, Pi.smul_apply, Matrix.col_apply, one_mul, smul_eq_mul]
  rw [dot_col_eq_mulVec, e8Cartan_diag]
  ring

theorem e8Form_reflect (i : Fin Tag.E8.rank) (u v : Fin Tag.E8.rank → ℤ) :
    e8Form (reflect8 i u) (reflect8 i v) = e8Form u v := by
  simp only [reflect8, reflect]
  exact e8Form_sub_sub_smul i u v

theorem e8Form_smul (w : WeylGroup .E8) (u v : Fin Tag.E8.rank → ℤ) :
    e8Form (w • u) (w • v) = e8Form u v := by
  induction w using (coxeterSystem .E8).simple_induction_left generalizing u v with
  | one => simp
  | mul_simple_left w i ih =>
      rw [mul_smul, mul_smul, simple_smul, simple_smul]
      exact (e8Form_reflect i (w • u) (w • v)).trans (ih u v)

@[expose] def fVec : Fin Tag.E8.rank → (Fin Tag.E8.rank → ℤ) :=
  ![![2, 3, 4, 6, 5, 4, 3, 2], ![2, 2, 3, 4, 3, 2, 1, 0],
    ![0, 1, 1, 2, 2, 2, 1, 0], ![0, 1, 1, 2, 1, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0]]

@[expose] def fIdx : Fin Tag.E8.rank → Fin 240 := ![0, 23, 59, 88, 113, 115, 117, 118]

theorem fVec_eq : ∀ (j k : Fin Tag.E8.rank), fVec j k = e8Root (fIdx j) k := by
  decide +kernel

theorem fVec_eq_fun (j : Fin Tag.E8.rank) : fVec j = e8Root (fIdx j) := by
  funext k
  exact fVec_eq j k

theorem f_orthogonal : ∀ i j : Fin Tag.E8.rank, i ≠ j → e8Form (fVec i) (fVec j) = 0 := by
  decide +kernel

@[expose] def cMat : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 1, -1, -1, 0, 0, -1, 0;
     0, 0, 0, 0, 0, 0, 0, 2;
     0, 0, 0, 0, 0, 0, 2, 0;
     0, 0, 0, 1, 0, -1, -1, -1;
     0, 0, 0, 0, 0, 2, 0, 0;
     0, 0, 1, -1, -1, -1, 0, 0;
     0, 0, 0, 0, 2, 0, 0, 0;
     1, -1, -1, 0, -1, 0, 0, 0]

theorem two_single_eq_sum : ∀ (i j : Fin Tag.E8.rank),
    ((2 : ℤ) • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) j =
      (∑ k : Fin Tag.E8.rank, cMat i k • fVec k) j := by
  decide +kernel

@[expose] def rootSet : Finset (Fin Tag.E8.rank → ℤ) := Finset.univ.image e8Root

@[expose] def orthRoots (k : ℕ) : Finset (Fin Tag.E8.rank → ℤ) :=
  rootSet.filter fun v => ∀ j : Fin Tag.E8.rank, j.val < k → e8Form v (fVec j) = 0

@[expose] def orthCount : Fin Tag.E8.rank → ℕ := ![240, 126, 60, 26, 8, 6, 4, 2]

theorem orthRoots_card : ∀ k : Fin Tag.E8.rank, (orthRoots k.val).card = orthCount k := by
  decide +kernel

theorem e8Root_reflect_fun : ∀ (k : Fin 240) (i : Fin Tag.E8.rank),
    reflect8 i (e8Root k) = e8Root (e8ReflIdx k i) := by
  intro k i
  funext j
  exact e8Root_reflect k i j

theorem rootSet_smul_mem (w : WeylGroup .E8) {v : Fin Tag.E8.rank → ℤ} (hv : v ∈ rootSet) :
    w • v ∈ rootSet := by
  induction w using (coxeterSystem .E8).simple_induction_left generalizing v with
  | one => simpa using hv
  | mul_simple_left w i ih =>
      rw [mul_smul, simple_smul]
      obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (by simpa only [rootSet] using ih hv)
      rw [← hk]
      change reflect8 i (e8Root k) ∈ rootSet
      rw [e8Root_reflect_fun]
      exact Finset.mem_image.mpr ⟨e8ReflIdx k i, Finset.mem_univ _, rfl⟩

theorem fVec_mem : ∀ j : Fin Tag.E8.rank, fVec j ∈ rootSet := by
  intro j
  rw [fVec_eq_fun]
  exact Finset.mem_image.mpr ⟨fIdx j, Finset.mem_univ _, rfl⟩

@[expose] def frameStab (k : ℕ) : Subgroup (WeylGroup .E8) where
  carrier := {w | ∀ j : Fin Tag.E8.rank, j.val < k → w • fVec j = fVec j}
  one_mem' := by
    intro j _
    simp
  mul_mem' := by
    intro a b ha hb j hj
    rw [mul_smul, hb j hj, ha j hj]
  inv_mem' := by
    intro a ha j hj
    calc a⁻¹ • fVec j = a⁻¹ • (a • fVec j) := by rw [ha j hj]
      _ = (a⁻¹ * a) • fVec j := (mul_smul a⁻¹ a (fVec j)).symm
      _ = fVec j := by simp

theorem frameStab_zero : frameStab 0 = ⊤ := by
  ext w
  simp [frameStab]

theorem frameStab_mono {a b : ℕ} (h : a ≤ b) : frameStab b ≤ frameStab a := by
  intro w hw j hj
  exact hw j (lt_of_lt_of_le hj h)

theorem two_single_eq_sum_fun (i : Fin Tag.E8.rank) :
    (2 : ℤ) • (Pi.single i 1 : Fin Tag.E8.rank → ℤ) = ∑ j, cMat i j • fVec j := by
  funext k
  exact two_single_eq_sum i k

theorem weyl_smul_zsmul (w : WeylGroup .E8) (c : ℤ) (v : Fin Tag.E8.rank → ℤ) :
    w • (c • v) = c • (w • v) :=
  smul_comm w c v

theorem two_zsmul_injective {u v : Fin Tag.E8.rank → ℤ}
    (h : (2 : ℤ) • u = (2 : ℤ) • v) : u = v := by
  funext k
  have hk := congrFun h k
  simp only [Pi.smul_apply, smul_eq_mul] at hk
  exact mul_right_injective₀ (by norm_num : (2 : ℤ) ≠ 0) hk

theorem frameStab_eight : frameStab 8 = ⊥ := by
  ext w
  constructor
  · intro hw
    rw [Subgroup.mem_bot]
    apply CFSG.LieType.Chevalley.ext_single
    intro i
    have hw' : ∀ j : Fin Tag.E8.rank, w • fVec j = fVec j := by
      intro j
      exact hw j j.isLt
    have h2 : w • ((2 : ℤ) • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) =
        (2 : ℤ) • (Pi.single i 1 : Fin Tag.E8.rank → ℤ) := by
      rw [two_single_eq_sum_fun i, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [weyl_smul_zsmul, hw' j]
    have h3 : (2 : ℤ) • (w • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) =
        (2 : ℤ) • (Pi.single i 1 : Fin Tag.E8.rank → ℤ) := by
      rw [← weyl_smul_zsmul, h2]
    simpa using two_zsmul_injective h3
  · intro hw
    rw [hw]
    exact (frameStab 8).one_mem

private theorem subgroup_card_le_card_mul_stabilizer {G V : Type*} [Group G] [MulAction G V]
    (H : Subgroup G) (x : V) (A : Finset V) (hA : ∀ y ∈ MulAction.orbit H x, y ∈ A) :
    Nat.card H ≤ A.card * Nat.card (MulAction.stabilizer H x) := by
  have h1 : Nat.card (MulAction.stabilizer H x) * (MulAction.orbit H x).ncard = Nat.card H := by
    rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]
  have h2 : (MulAction.orbit H x).ncard ≤ A.card := by
    rw [← Set.ncard_coe_finset A]
    exact Set.ncard_le_ncard hA
  calc
    Nat.card H = Nat.card (MulAction.stabilizer H x) * (MulAction.orbit H x).ncard := h1.symm
    _ ≤ Nat.card (MulAction.stabilizer H x) * A.card := Nat.mul_le_mul_left _ h2
    _ = A.card * Nat.card (MulAction.stabilizer H x) := Nat.mul_comm _ _

private theorem frameStab_step (k : Fin Tag.E8.rank) :
    Nat.card (frameStab k.val) ≤ orthCount k * Nat.card (frameStab (k.val + 1)) := by
  have hA : ∀ y ∈ MulAction.orbit (frameStab k.val) (fVec k), y ∈ orthRoots k.val := by
    rintro y ⟨w, rfl⟩
    have hroot : (w : WeylGroup .E8) • fVec k ∈ rootSet :=
      rootSet_smul_mem (w : WeylGroup .E8) (fVec_mem k)
    have hfix : ∀ j : Fin Tag.E8.rank, j.val < k.val → (w : WeylGroup .E8) • fVec j = fVec j :=
      fun j hj => w.2 j hj
    simp only [orthRoots, Finset.mem_filter]
    refine ⟨hroot, ?_⟩
    intro j hj
    calc e8Form ((w : WeylGroup .E8) • fVec k) (fVec j)
        = e8Form ((w : WeylGroup .E8) • fVec k) ((w : WeylGroup .E8) • fVec j) := by rw [hfix j hj]
      _ = e8Form (fVec k) (fVec j) := e8Form_smul (w : WeylGroup .E8) (fVec k) (fVec j)
      _ = 0 := f_orthogonal k j (by intro h; subst h; exact lt_irrefl _ hj)
  have hstab : MulAction.stabilizer (frameStab k.val) (fVec k) =
      (frameStab (k.val + 1)).subgroupOf (frameStab k.val) := by
    ext w
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hw j hj
      by_cases hjk : j.val < k.val
      · exact w.2 j hjk
      · have hjeq : j = k := by
          apply Fin.ext
          omega
        subst hjeq
        simpa only [Subgroup.smul_def] using hw
    · intro hw
      have h := hw k (Nat.lt_succ_self k.val)
      simpa only [Subgroup.smul_def] using h
  have hbound :=
    subgroup_card_le_card_mul_stabilizer (frameStab k.val) (fVec k) (orthRoots k.val) hA
  rw [orthRoots_card k, hstab] at hbound
  have hcard : Nat.card ((frameStab (k.val + 1)).subgroupOf (frameStab k.val)) =
      Nat.card (frameStab (k.val + 1)) := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (frameStab_mono (Nat.le_succ k.val))).toEquiv
  rwa [hcard] at hbound

private def orthProd : ℕ → ℕ
  | 0 => 1
  | n + 1 => orthProd n * (if h : n < 8 then orthCount ⟨n, h⟩ else 1)

private theorem card_le_orthProd_mul :
    ∀ n, n ≤ 8 → Nat.card (frameStab 0) ≤ orthProd n * Nat.card (frameStab n)
  | 0, _ => by simp [orthProd]
  | n + 1, hn => by
    have ih := card_le_orthProd_mul n (by omega)
    have hstep := frameStab_step ⟨n, by change n < 8; omega⟩
    have h8 : n < 8 := by omega
    calc Nat.card (frameStab 0) ≤ orthProd n * Nat.card (frameStab n) := ih
      _ ≤ orthProd n * (orthCount ⟨n, h8⟩ * Nat.card (frameStab (n + 1))) :=
        Nat.mul_le_mul_left _ hstep
      _ = orthProd (n + 1) * Nat.card (frameStab (n + 1)) := by
        rw [orthProd, dif_pos h8, mul_assoc]

theorem card_weylGroup_E8_le :
    Nat.card (CFSG.LieType.Chevalley.WeylGroup .E8) ≤ 18114969600 := by
  have h0 : Nat.card (frameStab 0) = Nat.card (WeylGroup .E8) := by
    rw [frameStab_zero, Subgroup.card_top]
  have h8 : Nat.card (frameStab 8) = 1 := by
    rw [frameStab_eight, Subgroup.card_bot]
  have hprod : orthProd 8 = 18114969600 := by decide
  have h := card_le_orthProd_mul 8 le_rfl
  rw [h0, h8, hprod, mul_one] at h
  exact h

theorem card_coxeterE8_group_le : Nat.card (CoxeterMatrix.E₈).Group ≤ 18114969600 := by
  have hC : GGIntCartan CoxeterMatrix.E₈ (Tag.cartan .E8) := by
    refine ⟨by decide, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have hM : CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .E8) = CoxeterMatrix.E₈ :=
    coxeterMatrix_eq_of_ggIntCartan (isFiniteType_cartan .E8) hC
  have h := card_weylGroup_E8_le
  change Nat.card ((CFSG.LieType.RootSystem.coxeterMatrix
    (isFiniteType_cartan .E8)).Group) ≤ 18114969600 at h
  rwa [hM] at h

end CFSG.StandardType.WeylE8Bound

end
